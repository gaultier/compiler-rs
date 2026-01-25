use std::{
    collections::{BTreeMap, HashMap},
    num::ParseIntError,
};

use crate::{
    error::{Error, ErrorKind},
    lex::{Lexer, Token, TokenKind},
    origin::{FileId, Origin},
    type_checker::{Type, TypeKind},
};
use serde::Serialize;

// TODO: u32?
#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
struct NodeId(usize);

#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
pub enum NodeKind {
    Number(u64),
    Bool(bool),
    Add(NodeId, NodeId),
    Multiply(NodeId, NodeId),
    Divide(NodeId, NodeId),
    Cmp(NodeId, NodeId),
    Identifier(String),
    FnCall {
        callee: NodeId,
        args: Vec<NodeId>,
    },
    FnDef {
        name: String,
        body: Vec<NodeId>,
    },
    Package(String),
    If {
        cond: NodeId,
        then_block: NodeId,
        else_block: NodeId,
    },
    For {
        cond: Option<NodeId>,
        block: Vec<NodeId>,
    },
    Block(Vec<NodeId>),
    VarDecl(String, NodeId), // TODO: Vec in case of identifier list.
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub kind: NodeKind,
    pub origin: Origin,
    pub typ: Type,
}

pub type FnNameToType = BTreeMap<String, (Type, Origin)>;
pub type VarNameToType = HashMap<String, Vec<(Type, Origin, usize /* Scope */)>>;

#[derive(Debug)]
pub struct Parser<'a> {
    error_mode: bool,
    pub tokens: Vec<Token>,
    tokens_consumed: usize,
    pub errors: Vec<Error>,
    input: &'a str,
    pub fn_name_to_type: FnNameToType,
    pub var_name_to_type: VarNameToType,
    current_scope: usize,
    file_id_to_name: &'a HashMap<FileId, String>,
    nodes: Vec<Node>,
}

impl<'a> Parser<'a> {
    pub fn new(
        input: &'a str,
        lexer: &Lexer,
        file_id_to_name: &'a HashMap<FileId, String>,
    ) -> Self {
        Self {
            error_mode: false,
            tokens: lexer.tokens.clone(),
            tokens_consumed: 0,
            errors: lexer.errors.clone(),
            input,
            fn_name_to_type: FnNameToType::new(),
            var_name_to_type: VarNameToType::new(),
            file_id_to_name,
            current_scope: 0,
            nodes: Vec::new(),
        }
    }

    fn new_node(&mut self, node: Node) -> NodeId {
        self.nodes.push(node);
        NodeId(self.nodes.len() - 1)
    }

    pub(crate) fn builtins(&mut self, cap_hint: usize) -> Vec<NodeId> {
        let mut res = Vec::with_capacity(cap_hint);

        let origin = Origin::new_builtin();
        let typ = Type::new_function(
            &Type::new_void(),
            &[Type::new_any()],
            &Origin::new_builtin(),
        );

        res.push(self.new_node(Node {
            kind: NodeKind::FnDef {
                name: String::from("println"),
                body: Vec::new(),
            },
            origin,
            typ,
        }));

        res
    }

    fn peek_token(&self) -> Option<&Token> {
        assert!(self.tokens_consumed <= self.tokens.len());
        if self.tokens_consumed == self.tokens.len() {
            None
        } else {
            Some(&self.tokens[self.tokens_consumed])
        }
    }

    // Used to avoid an avalanche of errors for the same line.
    fn skip_to_next_line(&mut self) {
        let current_line = self.peek_token().map(|t| t.origin.line).unwrap_or(1);

        loop {
            match self.peek_token() {
                None => return,
                Some(t) if t.kind == TokenKind::Eof || t.origin.line > current_line => {
                    self.tokens_consumed += 1;
                    return;
                }
                _ => {
                    self.tokens_consumed += 1;
                }
            };
        }
    }

    fn add_error_with_explanation(&mut self, kind: ErrorKind, origin: Origin, explanation: String) {
        if self.error_mode {
            return;
        }

        self.errors.push(Error::new(kind, origin, explanation));
        self.error_mode = true;

        // Skip to the next newline to avoid having cascading errors.
        self.skip_to_next_line();
    }

    fn match_kind(&mut self, kind: TokenKind) -> Option<Token> {
        match self.peek_token() {
            Some(t) if t.kind == kind => {
                let res = Some(*t);
                self.tokens_consumed += 1;
                res
            }
            _ => None,
        }
    }

    fn match_kind1_or_kind2(&mut self, kind1: TokenKind, kind2: TokenKind) -> Option<Token> {
        match self.peek_token() {
            Some(t) if t.kind == kind1 || t.kind == kind2 => {
                let res = Some(*t);
                self.tokens_consumed += 1;
                res
            }
            _ => None,
        }
    }

    fn parse_primary(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        if let Some(token) = self.match_kind(TokenKind::LiteralNumber) {
            let src = &self.input[token.origin.offset as usize..][..token.origin.len as usize];
            let num: u64 = match str::parse(src) {
                Ok(num) => num,
                Err::<_, ParseIntError>(err) => {
                    self.add_error_with_explanation(
                        ErrorKind::InvalidLiteralNumber,
                        token.origin,
                        err.to_string(),
                    );
                    return None;
                }
            };
            return Some(self.new_node(Node {
                kind: NodeKind::Number(num),
                origin: token.origin,
                typ: Type::new_int(),
            }));
        }
        if let Some(token) = self.match_kind(TokenKind::LiteralBool) {
            let src = &self.input[token.origin.offset as usize..][..token.origin.len as usize];

            assert!(src == "true" || src == "false");

            return Some(self.new_node(Node {
                kind: NodeKind::Bool(src == "true"),
                origin: token.origin,
                typ: Type::new_bool(),
            }));
        }

        if let Some(token) = self.match_kind(TokenKind::Identifier) {
            return Some(self.new_node(Node {
                kind: NodeKind::Identifier(
                    Self::str_from_source(self.input, &token.origin).to_owned(),
                ),
                origin: token.origin,
                typ: Type::default(), // Will be resolved.
            }));
        }

        None
    }

    fn parse_expr(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        self.parse_assignment()
    }

    fn parse_assignment(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }
        self.parse_logic_or()
    }

    fn parse_logic_or(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }
        self.parse_logic_and()
    }

    fn parse_logic_and(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }
        self.parse_equality()
    }

    fn parse_equality(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        let lhs = self.parse_comparison()?;
        if let Some(eq) = self.match_kind(TokenKind::EqEq) {
            if let Some(rhs) = self.parse_expr() {
                Some(self.new_node(Node {
                    kind: NodeKind::Cmp(lhs, rhs),
                    origin: eq.origin,
                    typ: Type::new_bool(),
                }))
            } else {
                let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                self.add_error_with_explanation(
                    ErrorKind::ParseCmpMissingRhs,
                    self.current_or_last_token_origin().unwrap_or(eq.origin),
                    format!("expected expression for the right-hand side of a == or != expression but found: {:?}",found),
                );
                None
            }
        } else {
            Some(lhs)
        }
    }

    fn parse_comparison(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }
        self.parse_term()
    }

    fn parse_term(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        let lhs = self.parse_factor()?;

        let token = match self.match_kind(TokenKind::Plus) {
            None => return Some(lhs),
            Some(t) => t,
        };

        let rhs = self.parse_term().or_else(||{
                let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                self.add_error_with_explanation(
                    ErrorKind::ParseTermMissingRhs,
                    self.current_or_last_token_origin().unwrap_or(token.origin),
                    format!("expected expression for the right-hand side of a + or - expression but found: {:?}",found),
                );
                None
            })?;

        Some(self.new_node(Node {
            kind: NodeKind::Add(lhs, rhs),
            origin: token.origin,
            typ: Type::default(),
        }))
    }

    fn parse_factor(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }
        let lhs = self.parse_unary()?;

        let token = match self.match_kind1_or_kind2(TokenKind::Star, TokenKind::Slash) {
            None => return Some(lhs),
            Some(t) => t,
        };

        let rhs = self.parse_factor().or_else(|| {
                let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                self.add_error_with_explanation(
                    ErrorKind::ParseFactorMissingRhs,
                    self.current_or_last_token_origin().unwrap_or(token.origin),
                    format!("expected expression for the right-hand side of a * or / expression but found: {:?}",found),
                );
                None
            })?;

        Some(self.new_node(Node {
            kind: if token.kind == TokenKind::Star {
                NodeKind::Multiply(lhs, rhs)
            } else {
                NodeKind::Divide(lhs, rhs)
            },
            origin: token.origin,
            typ: Type::default(),
        }))
    }

    fn parse_unary(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }
        self.parse_call()
    }

    fn parse_call(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        let callee = self.parse_primary()?;

        let lparen = if let Some(lparen) = self.match_kind(TokenKind::LeftParen) {
            lparen
        } else {
            return Some(callee);
        };

        let mut args = Vec::new();

        for _ in 0..self.remaining_tokens_count() {
            match self.peek_token() {
                Some(Token {
                    kind: TokenKind::RightParen,
                    ..
                }) => {
                    break;
                }
                Some(_) => {
                    let arg = self.parse_expr().or_else(|| {
                        self.errors.push(Error {
                            kind: ErrorKind::ParseCallMissingArgument,
                            origin: lparen.origin,
                            explanation: String::from(
                                "missing argument in function call, expected expression",
                            ),
                        });
                        None
                    })?;
                    args.push(arg);
                }
                None => {
                    self.errors.push(Error {
                        kind: ErrorKind::ParseCallMissingArgument,
                        origin: lparen.origin,
                        explanation: String::from(
                            "missing argument in function call, expected expression",
                        ),
                    });
                    return None;
                }
            }

            match self.peek_token() {
                Some(Token {
                    kind: TokenKind::Comma,
                    ..
                }) => {}
                Some(Token {
                    kind: TokenKind::RightParen,
                    ..
                }) => {
                    break;
                }
                _ => {
                    self.errors.push(Error {
                        kind: ErrorKind::MissingExpected(TokenKind::Comma),
                        origin: lparen.origin,
                        explanation: String::from(
                            "missing argument in function call, expected expression",
                        ),
                    });
                    return None;
                }
            }
        }

        self.expect_token_exactly_one(TokenKind::RightParen, "function call")?;

        Some(self.new_node(Node {
            kind: NodeKind::FnCall { callee, args },
            origin: lparen.origin,
            typ: Type::default(),
        }))
    }

    fn parse_statement_for(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        let keyword_for = self.match_kind(TokenKind::KeywordFor)?;
        let cond: Option<NodeId> = if self.match_kind(TokenKind::LeftCurly).is_some() {
            None
        } else {
            let cond = if let Some(cond) = self.parse_expr() {
                cond
            } else {
                self.add_error_with_explanation(
                    ErrorKind::MissingExpr,
                    keyword_for.origin,
                    String::from("expected expression following for keyword"),
                );
                return None;
            };

            self.expect_token_exactly_one(TokenKind::LeftCurly, "for body")?;
            Some(cond)
        };

        let mut stmts = Vec::new();

        for _ in 0..self.remaining_tokens_count() {
            match self.peek_token() {
                None
                | Some(Token {
                    kind: TokenKind::RightCurly,
                    ..
                }) => break,
                _ => {}
            }

            let stmt = self.parse_statement()?;
            stmts.push(stmt);
        }
        self.expect_token_exactly_one(TokenKind::RightCurly, "for body")?;

        Some(self.new_node(Node {
            kind: NodeKind::For { cond, block: stmts },
            origin: keyword_for.origin,
            typ: Type::new_void(),
        }))
    }

    fn parse_statement_if(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        let keyword_if = self.match_kind(TokenKind::KeywordIf)?;
        let cond = self.parse_expr()?;

        let left_curly = self.expect_token_exactly_one(TokenKind::LeftCurly, "if body")?;

        let mut stmts = Vec::new();

        for _ in 0..self.remaining_tokens_count() {
            match self.peek_token() {
                None
                | Some(Token {
                    kind: TokenKind::RightCurly,
                    ..
                }) => break,
                _ => {}
            }

            let stmt = self.parse_statement()?;
            stmts.push(stmt);
        }
        self.expect_token_exactly_one(TokenKind::RightCurly, "then body")?;

        let then_block = self.new_node(Node {
            kind: NodeKind::Block(stmts),
            origin: left_curly.origin,
            typ: Type::new_void(),
        });

        let else_stmts = if self.match_kind(TokenKind::KeywordElse).is_some() {
            let left_curly = self.expect_token_exactly_one(TokenKind::LeftCurly, "else body")?;
            let mut stmts = Vec::new();
            for _ in 0..self.remaining_tokens_count() {
                match self.peek_token() {
                    None
                    | Some(Token {
                        kind: TokenKind::RightCurly,
                        ..
                    }) => break,
                    _ => {}
                }

                let stmt = self.parse_statement()?;
                stmts.push(stmt);
            }
            self.expect_token_exactly_one(TokenKind::RightCurly, "else body")?;
            stmts
        } else {
            Vec::new()
        };
        let else_block = self.new_node(Node {
            kind: NodeKind::Block(stmts),
            origin: left_curly.origin,
            typ: Type::new_void(),
        });

        Some(self.new_node(Node {
            kind: NodeKind::If {
                cond,
                then_block,
                else_block,
            },
            origin: keyword_if.origin,
            typ: Type::new_void(),
        }))
    }

    // TODO: Support shot var decl: `x := 1`.
    // TODO: Support more forms.
    fn parse_statement_var_decl(&mut self) -> Option<NodeId> {
        let var = self.match_kind(TokenKind::KeywordVar)?;
        let identifier = self.expect_token_exactly_one(TokenKind::Identifier, "var declaration")?;
        let eq = self.expect_token_exactly_one(TokenKind::Eq, "var declaration")?;
        let expr = if let Some(expr) = self.parse_expr() {
            expr
        } else {
            let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
            self.add_error_with_explanation(
                ErrorKind::MissingExpr,
                eq.origin,
                format!(
                    "expected expression in variable declaration following '=' but found: {:?}",
                    found
                ),
            );
            return None;
        };

        let identifier_str = Self::str_from_source(self.input, &identifier.origin);
        let typ = self.nodes[expr].typ.clone();

        Some(self.new_node(Node {
            kind: NodeKind::VarDecl(identifier_str.to_owned(), expr),
            origin: var.origin,
            typ,
        }))
    }

    fn parse_statement(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        if let Some(stmt) = self.parse_statement_if() {
            return Some(stmt);
        };

        if let Some(stmt) = self.parse_statement_for() {
            return Some(stmt);
        };

        if let Some(stmt) = self.parse_statement_var_decl() {
            return Some(stmt);
        };

        self.parse_expr()
    }

    // Best effort to find the closest token when doing error reporting.
    fn current_or_last_token_origin(&self) -> Option<Origin> {
        assert!(self.tokens_consumed <= self.tokens.len());

        if self.tokens_consumed == self.tokens.len() {
            return self.tokens.last().map(|t| t.origin);
        }

        let token = &self.tokens[self.tokens_consumed];
        if token.kind != TokenKind::Eof {
            Some(token.origin)
        } else if self.tokens_consumed > 0 {
            Some(self.tokens[self.tokens_consumed - 1].origin)
        } else {
            None
        }
    }

    fn parse_package_clause(&mut self) -> Option<NodeId> {
        self.expect_token_exactly_one(TokenKind::KeywordPackage, "package clause")?;

        let package = if let Some(p) = self.match_kind(TokenKind::Identifier) {
            p
        } else {
            self.add_error_with_explanation(
                ErrorKind::MissingTopLevelPackage,
                self.current_or_last_token_origin().unwrap(),
                String::from("the package keyword must be followed by a package name"),
            );
            return None;
        };

        Some(self.new_node(Node {
            kind: NodeKind::Package(Self::str_from_source(self.input, &package.origin).to_owned()),
            origin: package.origin,
            typ: Type::new_void(),
        }))
    }

    fn str_from_source(src: &'a str, origin: &Origin) -> &'a str {
        &src[origin.offset as usize..origin.offset as usize + origin.len as usize]
    }

    fn remaining_tokens_count(&self) -> usize {
        self.tokens.len() - self.tokens_consumed
    }

    fn expect_token_exactly_one(&mut self, token_kind: TokenKind, context: &str) -> Option<Token> {
        if let Some(token) = self.match_kind(token_kind) {
            Some(token)
        } else {
            self.add_error_with_explanation(
                ErrorKind::MissingExpected(token_kind),
                self.current_or_last_token_origin().unwrap(),
                format!("failed to parse {}: missing {:#?}", context, token_kind),
            );
            None
        }
    }

    fn parse_function_declaration(&mut self) -> Option<NodeId> {
        let func = self.expect_token_exactly_one(TokenKind::KeywordFunc, "function declaration")?;

        let name = if let Some(name) = self.match_kind(TokenKind::Identifier) {
            name
        } else {
            self.add_error_with_explanation(
                ErrorKind::MissingExpected(TokenKind::Identifier),
                self.current_or_last_token_origin().unwrap(),
                String::from("failed to parse function declaration: missing function name"),
            );
            return None;
        };

        self.expect_token_exactly_one(TokenKind::LeftParen, "function declaration")?;

        // TODO: Args.

        self.expect_token_exactly_one(TokenKind::RightParen, "function declaration")?;

        // TODO: Return type.

        self.expect_token_exactly_one(TokenKind::LeftCurly, "function declaration")?;

        let mut stmts = Vec::new();

        for _ in 0..self.remaining_tokens_count() {
            match self.peek_token() {
                None
                | Some(Token {
                    kind: TokenKind::RightCurly,
                    ..
                }) => break,
                _ => {}
            }

            let stmt = self.parse_statement()?;
            stmts.push(stmt);
        }

        self.expect_token_exactly_one(TokenKind::RightCurly, "function declaration")?;

        Some(self.new_node(Node {
            kind: NodeKind::FnDef {
                name: Self::str_from_source(self.input, &name.origin).to_owned(),
                body: stmts,
            },
            origin: func.origin,
            typ: Type::new_function(&Type::new_void(), &[], &func.origin), // TODO
        }))
    }

    fn parse_declaration(&mut self) -> Option<NodeId> {
        if let Some(fn_def) = self.parse_function_declaration() {
            return Some(fn_def);
        }

        None
    }

    #[warn(unused_results)]
    pub fn parse(&mut self) -> Vec<NodeId> {
        let mut decls = Vec::new();
        let builtins = self.builtins(self.tokens.len());
        decls.extend(builtins);
        self.fn_name_to_type = FnNameToType::new();

        if let Some(p) = self.parse_package_clause() {
            decls.push(p);
        } else {
            return decls;
        }

        for _i in 0..self.tokens.len() {
            if self.peek_token().is_none() {
                return decls;
            }

            if self.error_mode {
                self.skip_to_next_line();
                self.error_mode = false;
                continue;
            }

            match self.peek_token().map(|t| t.kind) {
                None | Some(TokenKind::Eof) => break,
                token => {
                    if let Some(decl) = self.parse_declaration() {
                        decls.push(decl);
                        continue;
                    }

                    // Catch-all.
                    self.add_error_with_explanation(
                        ErrorKind::ParseDeclaration,
                        self.current_or_last_token_origin().unwrap(),
                        format!(
                            "catch-all parse declaration error: encountered unexpected token {:#?}",
                            token
                        ),
                    );
                }
            }
        }

        self.resolve_nodes(&mut decls);
        decls
    }

    fn resolve_node(&mut self, node_id: NodeId) {
        let node = &mut self.nodes[node_id];
        match &mut node.kind {
            // Nothing to do.
            NodeKind::Package(_) | NodeKind::Number(_) | NodeKind::Bool(_) => {}

            NodeKind::Identifier(name) => {
                if let Some((t, _)) = self.fn_name_to_type.get(name) {
                    node.typ = t.clone();
                } else if let Some(scopes) = self.var_name_to_type.get(name)
                    && let Some((t, _, _)) = scopes.last()
                {
                    node.typ = t.clone();
                }
            }

            // Recurse.
            NodeKind::Add(lhs, rhs)
            | NodeKind::Multiply(lhs, rhs)
            | NodeKind::Divide(lhs, rhs)
            | NodeKind::Cmp(lhs, rhs) => {
                self.resolve_node(lhs);
                self.resolve_node(rhs);
                if *node.typ.kind == TypeKind::Any {
                    node.typ = lhs.typ.clone();
                    assert_ne!(*node.typ.kind, TypeKind::Any);
                }
            }
            NodeKind::VarDecl(identifier, expr) => {
                self.resolve_node(expr);

                if let Some(scopes) = self.var_name_to_type.get(identifier)
                    && scopes
                        .last()
                        .map(|(_, _, scope)| *scope)
                        .unwrap_or_default()
                        == self.current_scope
                {
                    let prev_origin = scopes.last().map(|(_, origin, _)| origin).unwrap();
                    self.add_error_with_explanation(
                        ErrorKind::NameAlreadyDefined,
                        node.origin,
                        format!(
                            "variable redefines existing name, defined here: {}",
                            prev_origin.display(self.file_id_to_name)
                        ),
                    );
                }
                self.var_name_to_type
                    .entry(identifier.to_owned())
                    .or_default()
                    .push((node.typ.clone(), node.origin, self.current_scope));
            }
            NodeKind::FnCall { callee, args } => {
                self.resolve_node(callee);
                match &*callee.typ.kind {
                    TypeKind::Function(_, _) => {}
                    _ => {
                        self.errors.push(Error {
                            kind: ErrorKind::CallingANonFunction,
                            origin: node.origin,
                            explanation: format!("calling a non-function: {}", &callee.typ),
                        });
                    }
                }

                for op in args {
                    self.resolve_node(op)
                }
                if *node.typ.kind == TypeKind::Any {
                    node.typ = callee.typ.clone();
                }
            }
            NodeKind::Block(stmts) => {
                assert_eq!(*node.typ.kind, TypeKind::Void);

                for op in stmts {
                    self.resolve_node(op)
                }
            }
            NodeKind::FnDef { name, body } => {
                assert!(matches!(&*node.typ.kind, TypeKind::Function(_, _)));
                if let Some((old_typ, old_origin)) = self.fn_name_to_type.get(name) {
                    self.errors.push(Error::new_name_already_defined(
                        old_typ,
                        &node.typ,
                        name,
                        old_origin,
                        &node.origin,
                        self.file_id_to_name,
                    ));
                } else {
                    self.fn_name_to_type
                        .insert(name.to_owned(), (node.typ.clone(), node.origin));
                }

                // TODO: When supporting global variables and closures, this needs to be smarter
                // and only remove some entries.
                self.var_name_to_type.clear();

                for op in body {
                    self.resolve_node(op)
                }

                self.var_name_to_type.clear();
            }
            NodeKind::If {
                cond,
                then_block,
                else_block,
            } => {
                self.resolve_node(cond);
                self.resolve_node(then_block);
                self.resolve_node(else_block);
            }
            NodeKind::For { cond, block } => {
                if let Some(cond) = cond {
                    self.resolve_node(cond);
                }

                for stmt in block {
                    self.resolve_node(stmt)
                }
            }
        }
    }

    fn resolve_nodes(&mut self, nodes: &mut [Node]) {
        for node in nodes {
            self.resolve_node(node);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_number() {
        let input = "123 ";
        let mut lexer = Lexer::new(1);
        lexer.lex(&input);

        assert!(lexer.errors.is_empty());

        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let root = parser.parse_expr().unwrap();

        assert!(parser.errors.is_empty());

        {
            assert!(matches!(root.kind, NodeKind::Number(123)));
        }
    }

    #[test]
    fn parse_add() {
        let input = "123 + 45 + 0";
        let mut lexer = Lexer::new(1);
        lexer.lex(&input);

        assert!(lexer.errors.is_empty());

        let mut file_id_to_name = HashMap::new();
        file_id_to_name.insert(1, String::from("test.go"));

        let mut parser = Parser::new(input, &lexer, &file_id_to_name);
        let root = parser.parse_expr().unwrap();

        assert!(parser.errors.is_empty());

        match root.kind {
            NodeKind::Add(lhs, rhs) => {
                assert!(matches!(lhs.kind, NodeKind::Number(123)));
                match rhs.kind {
                    NodeKind::Add(mhs, rhs) => {
                        assert!(matches!(mhs.kind, NodeKind::Number(45)));
                        assert!(matches!(rhs.kind, NodeKind::Number(0)));
                    }
                    _ => panic!("Expected Add"),
                }
            }
            _ => panic!("Expected Add"),
        }
    }
}
