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

#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
pub enum NodeKind {
    Number(u64),
    Bool(bool),
    Add(Box<Node>, Box<Node>),
    Multiply(Box<Node>, Box<Node>),
    Divide(Box<Node>, Box<Node>),
    Identifier(String),
    FnCall {
        callee: Box<Node>,
        args: Vec<Node>,
    },
    FnDef {
        name: String,
        body: Vec<Node>,
    },
    Package(String),
    If {
        cond: Box<Node>,
        then_block: Option<Box<Node>>,
        else_block: Option<Box<Node>>,
    },
    Block(Vec<Node>),
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub kind: NodeKind,
    pub origin: Origin,
    pub typ: Type,
}

#[derive(Serialize, Clone, Copy, Debug)]
pub struct NodeIndex(usize);

pub type NameToType = BTreeMap<String, (Type, Origin)>;

#[derive(Debug)]
pub struct Parser<'a> {
    error_mode: bool,
    pub tokens: Vec<Token>,
    tokens_consumed: usize,
    pub errors: Vec<Error>,
    input: &'a str,
    pub name_to_type: NameToType,
    file_id_to_name: &'a HashMap<FileId, String>,
}

impl std::ops::Index<NodeIndex> for [Node] {
    type Output = Node;

    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self[index.0]
    }
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
            name_to_type: NameToType::new(),
            file_id_to_name,
        }
    }

    pub(crate) fn builtins(cap_hint: usize) -> Vec<Node> {
        let mut nodes = Vec::with_capacity(cap_hint);

        let origin = Origin::new_builtin();
        let typ = Type::new_function(
            &Type::new_void(),
            &[Type::new_any()],
            &Origin::new_builtin(),
        );

        nodes.push(Node {
            kind: NodeKind::FnDef {
                name: String::from("println"),
                body: Vec::new(),
            },
            origin,
            typ,
        });

        nodes
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

    fn parse_primary(&mut self) -> Option<Node> {
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
            return Some(Node {
                kind: NodeKind::Number(num),
                origin: token.origin,
                typ: Type::new_int(),
            });
        }
        if let Some(token) = self.match_kind(TokenKind::LiteralBool) {
            let src = &self.input[token.origin.offset as usize..][..token.origin.len as usize];

            assert!(src == "true" || src == "false");

            return Some(Node {
                kind: NodeKind::Bool(src == "true"),
                origin: token.origin,
                typ: Type::new_bool(),
            });
        }

        if let Some(token) = self.match_kind(TokenKind::Identifier) {
            return Some(Node {
                kind: NodeKind::Identifier(
                    Self::str_from_source(self.input, &token.origin).to_owned(),
                ),
                origin: token.origin,
                typ: Type::default(), // Will be resolved.
            });
        }

        None
    }

    fn parse_expr(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }

        self.parse_assignment()
    }

    fn parse_assignment(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }
        self.parse_logic_or()
    }

    fn parse_logic_or(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }
        self.parse_logic_and()
    }

    fn parse_logic_and(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }
        self.parse_equality()
    }

    fn parse_equality(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }
        self.parse_comparison()
    }

    fn parse_comparison(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }
        self.parse_term()
    }

    fn parse_term(&mut self) -> Option<Node> {
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

        Some(Node {
            kind: NodeKind::Add(Box::new(lhs), Box::new(rhs)),
            origin: token.origin,
            typ: Type::default(),
        })
    }

    fn parse_factor(&mut self) -> Option<Node> {
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

        Some(Node {
            kind: if token.kind == TokenKind::Star {
                NodeKind::Multiply(Box::new(lhs), Box::new(rhs))
            } else {
                NodeKind::Divide(Box::new(lhs), Box::new(rhs))
            },
            origin: token.origin,
            typ: Type::default(),
        })
    }

    fn parse_unary(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }
        self.parse_call()
    }

    fn parse_call(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }

        let f = self.parse_primary()?;

        let lparen = if let Some(lparen) = self.match_kind(TokenKind::LeftParen) {
            lparen
        } else {
            return Some(f);
        };

        let mut args = Vec::new();
        if self.peek_token().is_some_and(|t| t.kind != TokenKind::RightParen) {
            loop {
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

                if self.match_kind(TokenKind::Comma).is_none() {
                    break;
                }
            }
        }

        self.expect_token_exactly_one(TokenKind::RightParen, "function call")?;

        Some(Node {
            kind: NodeKind::FnCall {
                callee: Box::new(f),
                args,
            },
            origin: lparen.origin,
            typ: Type::default(),
        })
    }

    fn parse_statement_if(&mut self) -> Option<Node> {
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

        let then_block = if stmts.is_empty() {
            None
        } else {
            Some(Box::new(Node {
                kind: NodeKind::Block(stmts),
                origin: left_curly.origin,
                typ: Type::new_void(),
            }))
        };

        let else_block = if self.match_kind(TokenKind::KeywordElse).is_some() {
            let left_curly = self.expect_token_exactly_one(TokenKind::LeftCurly, "else body")?;
            let mut stmts = Vec::new();
            for _ in 0..self.remaining_tokens_count() {
                match self.peek_token() {
                    None | Some(Token {
                        kind: TokenKind::RightCurly,
                        ..
                    }) => break,
                    _ => {}
                }

                let stmt = self.parse_statement()?;
                stmts.push(stmt);
            }
            self.expect_token_exactly_one(TokenKind::RightCurly, "else body")?;
            if stmts.is_empty() {
                None
            } else {
                Some(Box::new(Node {
                    kind: NodeKind::Block(stmts),
                    origin: left_curly.origin,
                    typ: Type::new_void(),
                }))
            }
        } else {
            None
        };

        Some(Node {
            kind: NodeKind::If {
                cond: Box::new(cond),
                then_block,
                else_block,
            },
            origin: keyword_if.origin,
            typ: Type::new_void(),
        })
    }

    fn parse_statement(&mut self) -> Option<Node> {
        if self.error_mode {
            return None;
        }

        if let Some(stmt) = self.parse_statement_if() {
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

    fn parse_package_clause(&mut self) -> Option<Node> {
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

        Some(Node {
            kind: NodeKind::Package(Self::str_from_source(self.input, &package.origin).to_owned()),
            origin: package.origin,
            typ: Type::new_void(),
        })
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

    fn parse_function_declaration(&mut self) -> Option<Node> {
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

        Some(Node {
            kind: NodeKind::FnDef {
                name: Self::str_from_source(self.input, &name.origin).to_owned(),
                body: stmts,
            },
            origin: func.origin,
            typ: Type::new_function(&Type::new_void(), &[], &func.origin), // TODO
        })
    }

    fn parse_declaration(&mut self) -> Option<Node> {
        if let Some(fn_def) = self.parse_function_declaration() {
            return Some(fn_def);
        }

        None
    }

    #[warn(unused_results)]
    pub fn parse(&mut self) -> Vec<Node> {
        let mut decls = Vec::new();
        let builtins_nodes = Self::builtins(self.tokens.len());
        decls.extend_from_slice(&builtins_nodes);
        self.name_to_type = NameToType::new();

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

    fn resolve_node(&mut self, node: &mut Node) {
        match &mut node.kind {
            // Nothing to do.
            NodeKind::Package(_) | NodeKind::Number(_) | NodeKind::Bool(_) => {}

            NodeKind::Identifier(name) => {
                if let Some((t, _)) = self.name_to_type.get(name) {
                    node.typ = t.clone();
                }
            }

            // Recurse.
            NodeKind::Add(lhs, rhs)
            | NodeKind::Multiply(lhs, rhs)
            | NodeKind::Divide(lhs, rhs) => {
                self.resolve_node(lhs);
                self.resolve_node(rhs);
                if *node.typ.kind == TypeKind::Unknown {
                    node.typ = lhs.typ.clone();
                    assert_ne!(*node.typ.kind, TypeKind::Unknown);
                }
            }
            NodeKind::FnCall { callee, args } => {
                self.resolve_node(callee);
                for op in args {
                    self.resolve_node(op)
                }
                if *node.typ.kind == TypeKind::Unknown {
                    node.typ = callee.typ.clone();
                    assert_ne!(*node.typ.kind, TypeKind::Unknown);
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
                if let Some((old_typ, old_origin)) = self.name_to_type.get(name) {
                    self.errors.push(Error::new_name_already_defined(
                        old_typ,
                        &node.typ,
                        name,
                        old_origin,
                        &node.origin,
                        self.file_id_to_name,
                    ));
                } else {
                    self.name_to_type
                        .insert(name.to_owned(), (node.typ.clone(), node.origin));
                }

                for op in body {
                    self.resolve_node(op)
                }
            }
            NodeKind::If {
                cond,
                then_block,
                else_block,
            } => {
                self.resolve_node(&mut *cond);

                if let Some(then_block) = then_block {
                    self.resolve_node(then_block)
                }
                if let Some(else_block) = else_block {
                    self.resolve_node(else_block)
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
