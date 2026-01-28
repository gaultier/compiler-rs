use std::{
    collections::HashMap,
    hash::Hash,
    num::ParseIntError,
    ops::{Index, IndexMut},
};

use crate::{
    error::{Error, ErrorKind},
    lex::{Lexer, Token, TokenKind},
    origin::{FileId, Origin, OriginKind},
    type_checker::Type,
};
use serde::Serialize;

// TODO: u32?
#[derive(Serialize, Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct NodeId(pub(crate) usize);

#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
pub struct FnDef {
    pub(crate) name: String,
    pub(crate) args: Vec<NodeId>,
    pub(crate) ret: Option<NodeId>,
    pub(crate) body: NodeId,
}

#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
pub enum NodeKind {
    // TODO: Should we just use 'Block'?
    File(Vec<NodeId>), // Root.
    Number(u64),
    Bool(bool),
    Add(NodeId, NodeId),
    Multiply(NodeId, NodeId),
    Divide(NodeId, NodeId),
    Cmp(NodeId, NodeId),
    Identifier(String),
    Assignment(NodeId, TokenKind, NodeId),
    FnCall {
        // Can be a variable (function pointer), or a string.
        callee: NodeId,
        args: Vec<NodeId>,
    },
    FnDef(FnDef),
    Package(String),
    If {
        cond: NodeId,
        then_block: NodeId,
        else_block: Option<NodeId>,
    },
    For {
        cond: Option<NodeId>,
        block: NodeId,
    },
    Block(Vec<NodeId>),
    VarDecl(String, NodeId), // TODO: Vec in case of identifier list.
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub kind: NodeKind,
    pub origin: Origin,
}

impl IndexMut<NodeId> for [Node] {
    fn index_mut(&mut self, index: NodeId) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl Index<NodeId> for [Node] {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self[index.0]
    }
}

impl IndexMut<NodeId> for Vec<Node> {
    fn index_mut(&mut self, index: NodeId) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl Index<NodeId> for Vec<Node> {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self[index.0]
    }
}

#[derive(Debug)]
pub struct NameToDef {
    scopes: Vec<HashMap<String, NodeId>>,
    definitive: HashMap<String, NodeId>,
}

pub struct Parser<'a> {
    error_mode: bool,
    pub tokens: Vec<Token>,
    tokens_consumed: usize,
    pub errors: Vec<Error>,
    input: &'a str,
    file_id_to_name: &'a HashMap<FileId, String>,
    pub(crate) nodes: Vec<Node>,
    pub(crate) node_to_type: HashMap<NodeId, Type>,
    pub(crate) name_to_def: NameToDef,
}

#[derive(PartialEq, Eq)]
pub(crate) enum ScopeResolution {
    Current,
    Ancestor,
}

impl NameToDef {
    fn new() -> Self {
        Self {
            scopes: Vec::new(),
            definitive: HashMap::new(),
        }
    }

    pub(crate) fn get_scoped(&self, name: &str) -> Option<(&NodeId, ScopeResolution)> {
        self.scopes.iter().rev().enumerate().find_map(|(i, scope)| {
            scope.get(name).map(|node_id| {
                let scope = if i == self.scopes.len() - 1 {
                    ScopeResolution::Current
                } else {
                    ScopeResolution::Ancestor
                };
                (node_id, scope)
            })
        })
    }

    pub(crate) fn get_definitive(&self, name: &str) -> Option<&NodeId> {
        self.definitive.get(name)
    }

    pub(crate) fn insert(&mut self, name: String, node_id: NodeId) {
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name.to_owned(), node_id);
        self.definitive.insert(name, node_id);
    }

    fn enter(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn leave(&mut self) {
        self.scopes.pop();
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
            file_id_to_name,
            nodes: Vec::new(),
            node_to_type: HashMap::new(),
            name_to_def: NameToDef::new(),
        }
    }

    fn new_node(&mut self, node: Node) -> NodeId {
        self.nodes.push(node);
        NodeId(self.nodes.len() - 1)
    }

    pub(crate) fn builtins(&mut self) {
        assert!(self.nodes.is_empty());

        let origin = Origin::new_builtin();

        let root = self.new_node(Node {
            kind: NodeKind::File(Vec::new()),
            origin,
        });
        self.name_to_def.enter();

        let any = self.new_node(Node {
            kind: NodeKind::Identifier(String::from("any")),
            origin,
        });
        self.name_to_def.insert(String::from("any"), any);
        self.node_to_type.insert(any, Type::new_any());

        let body = self.new_node(Node {
            kind: NodeKind::Block(Vec::new()),
            origin,
        });

        let println = self.new_node(Node {
            kind: NodeKind::FnDef(FnDef {
                name: String::from("println"),
                args: vec![any],
                ret: None,
                body,
            }),
            origin,
        });
        let println_type = Type::new_function(
            &Type::new_void(),
            &[Type::new_any()],
            &Origin::new_builtin(),
        );
        self.nodes[root].kind.as_file_mut().unwrap().push(println);
        self.name_to_def.insert(String::from("println"), println);
        dbg!(&println, &println_type);
        self.node_to_type.insert(println, println_type);
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

    // Operand     = Literal | OperandName [ TypeArgs ] | "(" Expression ")" .
    // Literal     = BasicLit | CompositeLit | FunctionLit .
    // BasicLit    = int_lit | float_lit | imaginary_lit | rune_lit | string_lit .
    // OperandName = identifier | QualifiedIdent .
    fn parse_operand(&mut self) -> Option<NodeId> {
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
            let node_id = self.new_node(Node {
                kind: NodeKind::Number(num),
                origin: token.origin,
            });
            self.node_to_type.insert(node_id, Type::new_int());
            return Some(node_id);
        }
        if let Some(token) = self.match_kind(TokenKind::LiteralBool) {
            let src = &self.input[token.origin.offset as usize..][..token.origin.len as usize];

            assert!(src == "true" || src == "false");

            let node_id = self.new_node(Node {
                kind: NodeKind::Bool(src == "true"),
                origin: token.origin,
            });
            self.node_to_type.insert(node_id, Type::new_bool());
            return Some(node_id);
        }

        if let Some(token) = self.match_kind(TokenKind::Identifier) {
            return Some(self.new_node(Node {
                kind: NodeKind::Identifier(
                    Self::str_from_source(self.input, &token.origin).to_owned(),
                ),
                origin: token.origin,
            }));
        }

        None
    }

    // PrimaryExpr   = Operand |
    //                 Conversion |
    //                 MethodExpr |
    //                 PrimaryExpr Selector |
    //                 PrimaryExpr Index |
    //                 PrimaryExpr Slice |
    //                 PrimaryExpr TypeAssertion |
    //                 PrimaryExpr Arguments .
    fn parse_primary_expr(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        if let Some(op) = self.parse_operand() {
            return Some(op);
        }

        // TODO

        None
    }

    // Expression = UnaryExpr | Expression binary_op Expression .
    // binary_op  = "||" | "&&" | rel_op | add_op | mul_op .
    // rel_op     = "==" | "!=" | "<" | "<=" | ">" | ">=" .
    // add_op     = "+" | "-" | "|" | "^" .
    // mul_op     = "*" | "/" | "%" | "<<" | ">>" | "&" | "&^" .
    fn parse_expr(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        // TODO

        if let Some(unary) = self.parse_unary_expr() {
            return Some(unary);
        }

        let lhs = self.parse_expr().or_else(|| {
            let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
            self.add_error_with_explanation(
                ErrorKind::MissingExpr,
                self.current_or_last_token_origin()
                    .unwrap_or(Origin::new_unknown()),
                format!("expected expression but found: {:?}", found),
            );

            None
        })?;

        let token = self.peek_token();
        match token.map(|t| t.kind) {
            // TODO: More.
            Some(TokenKind::Plus) => {
                let op = self.match_kind(TokenKind::Plus).unwrap();

                let rhs = self.parse_expr().or_else(|| {
                    let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                    self.add_error_with_explanation(
                        ErrorKind::MissingExpr,
                        self.current_or_last_token_origin().unwrap_or(op.origin),
                        format!("expected expression but found: {:?}", found),
                    );

                    None
                })?;

                Some(self.new_node(Node {
                    kind: NodeKind::Add(lhs, rhs),
                    origin: op.origin,
                }))
            }
            // TODO: More.
            Some(TokenKind::Star) => {
                let op = self.match_kind(TokenKind::Star).unwrap();

                let rhs = self.parse_expr().or_else(|| {
                    let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                    self.add_error_with_explanation(
                        ErrorKind::MissingExpr,
                        self.current_or_last_token_origin().unwrap_or(op.origin),
                        format!("expected expression but found: {:?}", found),
                    );

                    None
                })?;

                Some(self.new_node(Node {
                    kind: NodeKind::Multiply(lhs, rhs),
                    origin: op.origin,
                }))
            }
            // TODO: More.
            Some(TokenKind::Slash) => {
                let op = self.match_kind(TokenKind::Slash).unwrap();

                let rhs = self.parse_expr().or_else(|| {
                    let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                    self.add_error_with_explanation(
                        ErrorKind::MissingExpr,
                        self.current_or_last_token_origin().unwrap_or(op.origin),
                        format!("expected expression but found: {:?}", found),
                    );

                    None
                })?;

                Some(self.new_node(Node {
                    kind: NodeKind::Divide(lhs, rhs),
                    origin: op.origin,
                }))
            }
            // TODO: More.
            Some(TokenKind::EqEq) => {
                let op = self.match_kind(TokenKind::EqEq).unwrap();

                let rhs = self.parse_expr().or_else(|| {
                    let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                    self.add_error_with_explanation(
                        ErrorKind::MissingExpr,
                        self.current_or_last_token_origin().unwrap_or(op.origin),
                        format!("expected expression but found: {:?}", found),
                    );

                    None
                })?;

                Some(self.new_node(Node {
                    kind: NodeKind::Cmp(lhs, rhs),
                    origin: op.origin,
                }))
            }
            other => {
                self.add_error_with_explanation(
                    ErrorKind::MissingBinaryOp,
                    self.current_or_last_token_origin()
                        .unwrap_or(token.unwrap().origin),
                    format!("expected binary operator but found: {:?}", other),
                );
                None
            }
        }
    }

    // UnaryExpr  = PrimaryExpr | unary_op UnaryExpr .
    // unary_op   = "+" | "-" | "!" | "^" | "*" | "&" | "<-" .

    fn parse_unary_expr(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        match self.peek_token().map(|t| t.kind) {
            // TODO: More
            Some(TokenKind::Plus | TokenKind::Star) => {
                todo!()
            }
            _ => self.parse_primary_expr(),
        }
    }

    // ForStmt   = "for" [ Condition | ForClause | RangeClause ] Block .
    // Condition = Expression .
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

            Some(cond)
        };

        let block = self.parse_statement_block().or_else(|| {
            let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
            self.add_error_with_explanation(
                ErrorKind::MissingExpected(TokenKind::LeftCurly),
                keyword_for.origin,
                format!("expect block following for, found: {:?}", found),
            );

            None
        })?;

        Some(self.new_node(Node {
            kind: NodeKind::For { cond, block },
            origin: keyword_for.origin,
        }))
    }

    // Block         = "{" StatementList "}" .
    // StatementList = { Statement ";" } .
    fn parse_statement_block(&mut self) -> Option<NodeId> {
        let left_curly = self.match_kind(TokenKind::LeftCurly)?;

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
        self.expect_token_one(TokenKind::RightCurly, "block")?;

        Some(self.new_node(Node {
            kind: NodeKind::Block(stmts),
            origin: left_curly.origin,
        }))
    }

    // IfStmt = "if" [ SimpleStmt ";" ] Expression Block [ "else" ( IfStmt | Block ) ] .
    fn parse_statement_if(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        let keyword_if = self.match_kind(TokenKind::KeywordIf)?;
        let cond = self.parse_expr()?;

        let then_block = if let Some(b) = self.parse_statement_block() {
            b
        } else {
            let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
            self.add_error_with_explanation(
                ErrorKind::MissingExpected(TokenKind::LeftCurly),
                keyword_if.origin,
                format!("expect block following if(cond), found: {:?}", found),
            );

            return None;
        };

        let else_block = if self.match_kind(TokenKind::KeywordElse).is_some() {
            let block = self.parse_statement_block().or_else(|| {
                let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                self.add_error_with_explanation(
                    ErrorKind::MissingExpected(TokenKind::LeftCurly),
                    keyword_if.origin,
                    format!("expect block following else, found: {:?}", found),
                );

                None
            })?;

            Some(block)
        } else {
            None
        };

        Some(self.new_node(Node {
            kind: NodeKind::If {
                cond,
                then_block,
                else_block,
            },
            origin: keyword_if.origin,
        }))
    }

    // VarDecl = "var" ( VarSpec | "(" { VarSpec ";" } ")" ) .
    // VarSpec = IdentifierList ( Type [ "=" ExpressionList ] | "=" ExpressionList ) .
    fn parse_statement_var_decl(&mut self) -> Option<NodeId> {
        let var = self.match_kind(TokenKind::KeywordVar)?;
        let identifier = self.expect_token_one(TokenKind::Identifier, "var declaration")?;
        let eq = self.expect_token_one(TokenKind::Eq, "var declaration")?;
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

        Some(self.new_node(Node {
            kind: NodeKind::VarDecl(identifier_str.to_owned(), expr),
            origin: var.origin,
        }))
    }

    // Assignment = ExpressionList assign_op ExpressionList .
    fn parse_assignment(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }
        // TODO: Expression list.

        let lhs = self.parse_expr()?;
        // TODO: More operators.
        let eq = self.expect_token_one(TokenKind::Eq, "assignment")?;
        let rhs = self.parse_expr().or_else(|| {
            let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
            self.add_error_with_explanation(
                ErrorKind::MissingExpr,
                eq.origin,
                format!("expected expression in assignment, found: {:?}", found),
            );
            None
        })?;

        Some(self.new_node(Node {
            kind: NodeKind::Assignment(lhs, eq.kind, rhs),
            origin: eq.origin,
        }))
    }

    // SimpleStmt = EmptyStmt | ExpressionStmt | SendStmt | IncDecStmt | Assignment | ShortVarDecl .
    fn parse_simple_statement(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        // TODO: EmptyStmt ???
        if let Some(expr_stmt) = self.parse_expr() {
            return Some(expr_stmt);
        }

        // TODO: SendStmt.
        // TODO: IncDecStmt.

        if let Some(stmt) = self.parse_assignment() {
            return Some(stmt);
        };

        // TODO: ShortVarDecl.

        None
    }

    // Statement  = Declaration | LabeledStmt | SimpleStmt |
    //              GoStmt | ReturnStmt | BreakStmt | ContinueStmt | GotoStmt |
    //              FallthroughStmt | Block | IfStmt | SwitchStmt | SelectStmt | ForStmt |
    //              DeferStmt .
    fn parse_statement(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        if let Some(stmt) = self.parse_declaration() {
            return Some(stmt);
        }

        // TODO: Labeled stmt.

        if let Some(stmt) = self.parse_simple_statement() {
            return Some(stmt);
        }

        // TODO: Go stmt.
        // TODO: Return stmt.
        // TODO: Break stmt.
        // TODO: Continue stmt.
        // TODO: Goto stmt.
        // TODO: Fallthrough stmt.

        if let Some(stmt) = self.parse_statement_block() {
            return Some(stmt);
        };

        if let Some(stmt) = self.parse_statement_if() {
            return Some(stmt);
        };

        // TODO: Switch stmt.
        // TODO: Select stmt.

        if let Some(stmt) = self.parse_statement_for() {
            return Some(stmt);
        };

        // TODO: Defer stmt.

        None
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

    // PackageClause = "package" PackageName .
    // PackageName   = identifier .
    fn parse_package_clause(&mut self) -> Option<NodeId> {
        self.expect_token_one(TokenKind::KeywordPackage, "package clause")?;
        let package = self.expect_token_one(TokenKind::Identifier, "package clause")?;

        Some(self.new_node(Node {
            kind: NodeKind::Package(Self::str_from_source(self.input, &package.origin).to_owned()),
            origin: package.origin,
        }))
    }

    fn str_from_source(src: &'a str, origin: &Origin) -> &'a str {
        &src[origin.offset as usize..origin.offset as usize + origin.len as usize]
    }

    fn remaining_tokens_count(&self) -> usize {
        self.tokens.len() - self.tokens_consumed
    }

    fn expect_token_one(&mut self, token_kind: TokenKind, context: &str) -> Option<Token> {
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

    // FunctionDecl = "func" FunctionName [ TypeParameters ] Signature [ FunctionBody ] .
    // FunctionName = identifier .
    //Signature     = Parameters [ Result ] .
    // Result        = Parameters | Type .
    // Parameters    = "(" [ ParameterList [ "," ] ] ")" .
    // ParameterList = ParameterDecl { "," ParameterDecl } .
    // ParameterDecl = [ IdentifierList ] [ "..." ] Type .
    // FunctionBody = Block .
    fn parse_function_declaration(&mut self) -> Option<NodeId> {
        let func = self.match_kind(TokenKind::KeywordFunc)?;
        let name = self.expect_token_one(TokenKind::Identifier, "function declaration")?;
        self.expect_token_one(TokenKind::LeftParen, "function declaration")?;

        // TODO: Args.

        let rparen = self.expect_token_one(TokenKind::RightParen, "function declaration")?;

        // TODO: Return type.

        let body = if let Some(b) = self.parse_statement_block() {
            b
        } else {
            let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
            self.add_error_with_explanation(
                ErrorKind::MissingExpected(TokenKind::LeftCurly),
                rparen.origin,
                format!(
                    "expect block following function signature, found: {:?}",
                    found
                ),
            );

            return None;
        };

        let name = Self::str_from_source(self.input, &name.origin).to_owned();
        let node_id = self.new_node(Node {
            kind: NodeKind::FnDef(FnDef {
                name,
                args: vec![], // TODO
                ret: None,    // TODO
                body,
            }),
            origin: func.origin,
        });
        Some(node_id)
    }

    // Declaration  = ConstDecl | TypeDecl | VarDecl .
    fn parse_declaration(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        // TODO: Const decl.
        // TODO: Type decl.

        if let Some(stmt) = self.parse_statement_var_decl() {
            return Some(stmt);
        };

        None
    }

    // TopLevelDecl = Declaration | FunctionDecl | MethodDecl
    fn parse_top_level_declaration(&mut self) -> Option<NodeId> {
        if self.error_mode {
            return None;
        }

        if let Some(fn_def) = self.parse_declaration() {
            return Some(fn_def);
        }

        if let Some(fn_def) = self.parse_function_declaration() {
            return Some(fn_def);
        }

        // TODO: Methods.

        None
    }

    // SourceFile = PackageClause ";" { ImportDecl ";" } { TopLevelDecl ";" } .
    fn parse_source_file(&mut self) {
        assert!(!self.error_mode);
        self.builtins();
        assert!(!self.error_mode);

        self.parse_package_clause();

        // TODO: imports.

        for _i in 0..self.tokens.len() {
            let token = match self.peek_token().map(|t| t.kind) {
                None | Some(TokenKind::Eof) => break,
                Some(t) => t,
            };

            if self.error_mode {
                self.skip_to_next_line();
                self.error_mode = false;
                continue;
            }

            if let Some(decl) = self.parse_top_level_declaration() {
                self.nodes[0].kind.as_file_mut().unwrap().push(decl);
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

        self.resolve_nodes();
    }

    #[warn(unused_results)]
    pub fn parse(&mut self) {
        self.parse_source_file();

        self.resolve_nodes();
    }

    fn resolve_node(
        node_id: NodeId,
        nodes: &[Node],
        errors: &mut Vec<Error>,
        name_to_def: &mut NameToDef,
        file_id_to_name: &'a HashMap<FileId, String>,
    ) {
        let node = &nodes[node_id];
        if !matches!(node.kind, NodeKind::File(_)) && node.origin.kind == OriginKind::Builtin {
            return;
        }

        match &node.kind {
            NodeKind::File(decls) => {
                // Already called `.enter()` for builtins.
                assert_eq!(name_to_def.scopes.len(), 1);

                for decl in decls {
                    Self::resolve_node(*decl, nodes, errors, name_to_def, file_id_to_name);
                }

                name_to_def.leave();
            }
            // Nothing to do.
            NodeKind::Package(_) | NodeKind::Number(_) | NodeKind::Bool(_) => {}

            NodeKind::Assignment(lhs, _, rhs) => {
                Self::resolve_node(*lhs, nodes, errors, name_to_def, file_id_to_name);
                Self::resolve_node(*rhs, nodes, errors, name_to_def, file_id_to_name);
            }

            NodeKind::Identifier(name) => {
                dbg!(name, &name_to_def, node_id, &node.kind);

                let def_id = if let Some((def_id, _)) = name_to_def.get_scoped(name) {
                    def_id
                } else {
                    errors.push(Error::new(
                        ErrorKind::UnknownIdentifier,
                        node.origin,
                        format!("unknown identifier: {}", name),
                    ));
                    return;
                };

                let def = &nodes[*def_id];

                match def.kind {
                    NodeKind::FnDef { .. } => {}
                    NodeKind::VarDecl(_, _) => {}
                    NodeKind::Identifier(_) => {}
                    _ => {
                        panic!("identifier refers to invalid node: {:?}", def);
                    }
                }
            }

            // Recurse.
            NodeKind::Add(lhs, rhs)
            | NodeKind::Multiply(lhs, rhs)
            | NodeKind::Divide(lhs, rhs)
            | NodeKind::Cmp(lhs, rhs) => {
                Self::resolve_node(*lhs, nodes, errors, name_to_def, file_id_to_name);
                Self::resolve_node(*rhs, nodes, errors, name_to_def, file_id_to_name);
            }
            NodeKind::VarDecl(identifier, expr) => {
                Self::resolve_node(*expr, nodes, errors, name_to_def, file_id_to_name);

                if let Some((prev, scope)) = name_to_def.get_scoped(identifier)
                    && scope == ScopeResolution::Current
                {
                    let prev_origin = nodes[*prev].origin;
                    errors.push(Error::new(
                        ErrorKind::NameAlreadyDefined,
                        node.origin,
                        format!(
                            "{} redeclared, already declared here: {}",
                            identifier,
                            prev_origin.display(file_id_to_name)
                        ),
                    ));
                }

                name_to_def.insert(identifier.to_owned(), node_id);
                dbg!(identifier, node_id, &node.kind);
            }
            NodeKind::FnCall { callee, args } => {
                Self::resolve_node(*callee, nodes, errors, name_to_def, file_id_to_name);
                let callee_name = nodes[*callee].kind.as_identifier().unwrap();
                let def_id = name_to_def.get_scoped(callee_name);
                if def_id.is_none() {
                    errors.push(Error {
                        kind: ErrorKind::UnknownIdentifier,
                        origin: node.origin,
                        explanation: format!("unknown identifier: {}", callee_name),
                    });

                    // TODO: Should we pretend we found it?
                    return;
                }
                let def = &nodes[*def_id.unwrap().0];

                match def.kind {
                    NodeKind::FnDef { .. } => {} // All good.
                    _ => {
                        // Once function pointers are supported, VarDecl is also a viable option.
                        errors.push(Error {
                            kind: ErrorKind::CallingANonFunction,
                            origin: node.origin,
                            explanation: String::from("calling a non-function"),
                        });
                    }
                }

                for op in args {
                    Self::resolve_node(*op, nodes, errors, name_to_def, file_id_to_name);
                }
            }
            NodeKind::Block(stmts) => {
                name_to_def.enter();

                for op in stmts {
                    Self::resolve_node(*op, nodes, errors, name_to_def, file_id_to_name);
                }

                name_to_def.leave();
            }
            NodeKind::FnDef(FnDef {
                name,
                args,
                ret,
                body,
            }) => {
                if let Some((prev, _)) = name_to_def.get_scoped(name) {
                    let prev = &nodes[*prev];
                    errors.push(Error::new(
                        ErrorKind::NameAlreadyDefined,
                        node.origin,
                        format!(
                            "name {} already defined here: {}",
                            name,
                            prev.origin.display(file_id_to_name)
                        ),
                    ));
                }
                // TODO: Check shadowing of function name?
                name_to_def.insert(name.to_owned(), node_id);

                for arg in args {
                    Self::resolve_node(*arg, nodes, errors, name_to_def, file_id_to_name);
                }

                if let Some(ret) = ret {
                    Self::resolve_node(*ret, nodes, errors, name_to_def, file_id_to_name);
                }

                Self::resolve_node(*body, nodes, errors, name_to_def, file_id_to_name);
            }
            NodeKind::If {
                cond,
                then_block,
                else_block,
            } => {
                Self::resolve_node(*cond, nodes, errors, name_to_def, file_id_to_name);
                Self::resolve_node(*then_block, nodes, errors, name_to_def, file_id_to_name);
                if let Some(else_block) = else_block {
                    Self::resolve_node(*else_block, nodes, errors, name_to_def, file_id_to_name);
                }
            }
            NodeKind::For { cond, block } => {
                if let Some(cond) = cond {
                    Self::resolve_node(*cond, nodes, errors, name_to_def, file_id_to_name);
                }

                Self::resolve_node(*block, nodes, errors, name_to_def, file_id_to_name);
            }
        }
    }

    fn resolve_nodes(&mut self) {
        assert!(!self.nodes.is_empty());

        Self::resolve_node(
            NodeId(0),
            &self.nodes,
            &mut self.errors,
            &mut self.name_to_def,
            self.file_id_to_name,
        );
    }
}

impl NodeKind {
    fn as_file_mut(&mut self) -> Option<&mut Vec<NodeId>> {
        match self {
            NodeKind::File(v) => Some(v),
            _ => None,
        }
    }

    pub(crate) fn as_identifier(&self) -> Option<&str> {
        match self {
            NodeKind::Identifier(s) => Some(s),
            _ => None,
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
        let root_id = parser.parse_expr().unwrap();
        let root = &parser.nodes[root_id];

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
        let root_id = parser.parse_expr().unwrap();
        let root = &parser.nodes[root_id];

        assert!(parser.errors.is_empty());

        match &root.kind {
            NodeKind::Add(lhs, rhs) => {
                let lhs = &parser.nodes[*lhs];
                assert!(matches!(lhs.kind, NodeKind::Number(123)));
                let rhs = &parser.nodes[*rhs];
                match rhs.kind {
                    NodeKind::Add(mhs, rhs) => {
                        let mhs = &parser.nodes[mhs];
                        let rhs = &parser.nodes[rhs];
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
