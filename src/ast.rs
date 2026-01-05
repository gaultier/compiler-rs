use std::{collections::BTreeMap, num::ParseIntError};

use crate::{
    error::{Error, ErrorKind},
    lex::{Lexer, Token, TokenKind},
    origin::Origin,
    type_checker::{Type, TypeKind},
};
use serde::Serialize;

#[derive(Serialize, Copy, Clone, PartialEq, Eq, Debug)]
pub enum NodeKind {
    Number,
    Bool,
    Add,
    Multiply,
    Divide,
    Identifier,
    FnCall,
    FnDef,
    Package,
}

#[derive(Serialize, Clone, Debug)]
pub enum NodeData {
    Num(u64),
    Bool(bool),
    String(String),
}

#[derive(Serialize, Clone, Debug)]
pub struct Node {
    pub kind: NodeKind,
    pub data: Option<NodeData>,
    pub origin: Origin,
    pub typ: Type,
}

pub type NodeIndex = usize;

pub type NameToNodeDef = BTreeMap<String, NodeIndex>;

#[derive(Debug)]
pub struct Parser<'a> {
    error_mode: bool,
    pub tokens: Vec<Token>,
    tokens_consumed: usize,
    pub errors: Vec<Error>,
    pub nodes: Vec<Node>,
    input: &'a str,
    pub name_to_node_def: NameToNodeDef,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str, lexer: &Lexer) -> Self {
        let (builtins_nodes, builtin_names) = Self::builtins(lexer.tokens.len());
        Self {
            error_mode: false,
            tokens: lexer.tokens.clone(),
            tokens_consumed: 0,
            errors: lexer.errors.clone(),
            nodes: builtins_nodes,
            input,
            name_to_node_def: builtin_names,
        }
    }

    pub(crate) fn builtins(cap_hint: usize) -> (Vec<Node>, NameToNodeDef) {
        let mut nodes = Vec::with_capacity(cap_hint);
        let mut names = NameToNodeDef::new();

        nodes.push(Node {
            kind: NodeKind::FnDef,
            data: Some(NodeData::String(String::from("builtin.println"))),
            origin: Origin::new_builtin(),
            typ: Type::new_function(
                &Type::new_void(),
                &[Type::new_int()],
                &Origin::new_builtin(),
            ),
        });
        names.insert(String::from("builtin.println"), nodes.len() - 1);

        (nodes, names)
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

    fn parse_primary(&mut self) -> bool {
        if self.error_mode {
            return false;
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
                    return false;
                }
            };
            let node = Node {
                kind: NodeKind::Number,
                data: Some(NodeData::Num(num)),
                origin: token.origin,
                typ: Type::new_int(),
            };
            self.nodes.push(node);
            return true;
        }
        if let Some(token) = self.match_kind(TokenKind::LiteralBool) {
            let src = &self.input[token.origin.offset as usize..][..token.origin.len as usize];

            assert!(src == "true" || src == "false");

            let node = Node {
                kind: NodeKind::Bool,
                data: Some(NodeData::Bool(src == "true")),
                origin: token.origin,
                typ: Type::new_bool(),
            };
            self.nodes.push(node);
            return true;
        }

        if let Some(token) = self.match_kind(TokenKind::Identifier) {
            let node = Node {
                kind: NodeKind::Identifier,
                data: None,
                origin: token.origin,
                typ: Type::new_function(
                    &Type::new_void(),
                    &[Type::new_int()],
                    &Origin::new_builtin(),
                ),
            };
            self.nodes.push(node);
            return true;
        }

        false
    }

    fn parse_expr(&mut self) -> bool {
        if self.error_mode {
            return false;
        }

        if self.parse_assignement() {
            return true;
        }

        false
    }

    fn parse_assignement(&mut self) -> bool {
        if self.error_mode {
            return false;
        }
        self.parse_logic_or()
    }

    fn parse_logic_or(&mut self) -> bool {
        if self.error_mode {
            return false;
        }
        self.parse_logic_and()
    }

    fn parse_logic_and(&mut self) -> bool {
        if self.error_mode {
            return false;
        }
        self.parse_equality()
    }

    fn parse_equality(&mut self) -> bool {
        if self.error_mode {
            return false;
        }
        self.parse_comparison()
    }

    fn parse_comparison(&mut self) -> bool {
        if self.error_mode {
            return false;
        }
        self.parse_term()
    }

    fn parse_term(&mut self) -> bool {
        if self.error_mode {
            return false;
        }
        if !self.parse_factor() {
            return false;
        }

        loop {
            let token = match self.match_kind(TokenKind::Plus) {
                None => return true,
                Some(t) => t,
            };

            if !self.parse_factor() {
                let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                self.add_error_with_explanation(
                    ErrorKind::ParseTermMissingRhs,
                    self.current_or_last_token_origin().unwrap_or(token.origin),
                    format!("expected expression for the right-hand side of a + or - expression but found: {:?}",found),
                );
                return false;
            }

            let node = Node {
                kind: NodeKind::Add,
                data: None,
                origin: token.origin,
                typ: Type::default(),
            };
            self.nodes.push(node);
        }
    }

    fn parse_factor(&mut self) -> bool {
        if self.error_mode {
            return false;
        }
        if !self.parse_unary() {
            return false;
        }

        loop {
            let token = match self.match_kind1_or_kind2(TokenKind::Star, TokenKind::Slash) {
                None => return true,
                Some(t) => t,
            };

            if !self.parse_unary() {
                let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                self.add_error_with_explanation(
                    ErrorKind::ParseFactorMissingRhs,
                    self.current_or_last_token_origin().unwrap_or(token.origin),
                    format!("expected expression for the right-hand side of a * or / expression but found: {:?}",found),
                );
                return false;
            }

            let node = Node {
                kind: if token.kind == TokenKind::Star {
                    NodeKind::Multiply
                } else {
                    NodeKind::Divide
                },
                data: None,
                origin: token.origin,
                typ: Type::default(),
            };
            self.nodes.push(node);
        }
    }

    fn parse_unary(&mut self) -> bool {
        if self.error_mode {
            return false;
        }
        self.parse_call()
    }

    fn parse_call(&mut self) -> bool {
        if self.error_mode {
            return false;
        }

        if !self.parse_primary() {
            return false;
        }

        let lparen = if let Some(lparen) = self.match_kind(TokenKind::LeftParen) {
            lparen
        } else {
            return true;
        };

        let args_count = 1;
        if !self.parse_expr() {
            self.errors.push(Error {
                kind: ErrorKind::ParseCallMissingArgument,
                origin: lparen.origin,
                explanation: String::from("missing argument in function call, expected expression"),
            });
        }

        if self
            .expect_token_exactly_one(TokenKind::RightParen, "function call")
            .is_none()
        {
            return false;
        }

        let node = Node {
            kind: NodeKind::FnCall,
            data: Some(NodeData::Num(args_count)),
            origin: lparen.origin,
            typ: Type::default(),
        };
        self.nodes.push(node);

        true
    }

    fn parse_statement(&mut self) -> bool {
        if self.error_mode {
            return false;
        }

        if !self.parse_expr() {
            return false;
        }

        true
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

    fn parse_package_clause(&mut self) -> bool {
        if self
            .expect_token_exactly_one(TokenKind::KeywordPackage, "package clause")
            .is_none()
        {
            return false;
        }

        let package = if let Some(p) = self.match_kind(TokenKind::Identifier) {
            p
        } else {
            self.add_error_with_explanation(
                ErrorKind::MissingTopLevelPackage,
                self.current_or_last_token_origin().unwrap(),
                String::from("the package keyword must be followed by a package name"),
            );
            return false;
        };

        self.nodes.push(Node {
            kind: NodeKind::Package,
            data: Some(NodeData::String(
                Self::str_from_source(&self.input, &package.origin).to_owned(),
            )),
            origin: package.origin,
            typ: Type::new_void(),
        });

        true
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
            return None;
        }
    }

    fn parse_function_declaration(&mut self) -> bool {
        let func = if let Some(func) =
            self.expect_token_exactly_one(TokenKind::KeywordFunc, "function declaration")
        {
            func
        } else {
            return false;
        };

        let name = if let Some(name) = self.match_kind(TokenKind::Identifier) {
            name
        } else {
            self.add_error_with_explanation(
                ErrorKind::MissingExpected(TokenKind::Identifier),
                self.current_or_last_token_origin().unwrap(),
                String::from("failed to parse function declaration: missing function name"),
            );
            return false;
        };

        if self
            .expect_token_exactly_one(TokenKind::LeftParen, "function declaration")
            .is_none()
        {
            return false;
        }

        // TODO: Args.

        if self
            .expect_token_exactly_one(TokenKind::RightParen, "function declaration")
            .is_none()
        {
            return false;
        }

        // TODO: Return type.

        if self
            .expect_token_exactly_one(TokenKind::LeftCurly, "function declaration")
            .is_none()
        {
            return false;
        }

        for _ in 0..self.remaining_tokens_count() {
            match self.peek_token() {
                None
                | Some(Token {
                    kind: TokenKind::RightCurly,
                    ..
                }) => break,
                _ => {}
            }

            if !self.parse_statement() {
                return false;
            }
        }

        if self
            .expect_token_exactly_one(TokenKind::RightCurly, "function declaration")
            .is_none()
        {
            return false;
        }

        self.nodes.push(Node {
            kind: NodeKind::FnDef,
            data: Some(NodeData::String(
                Self::str_from_source(&self.input, &name.origin).to_owned(),
            )),
            origin: func.origin,
            typ: Type::new_function(&Type::new_void(), &[], &func.origin), // TODO
        });

        true
    }

    fn parse_declaration(&mut self) -> bool {
        if self.parse_function_declaration() {
            return true;
        }

        false
    }

    pub fn parse(&mut self) {
        self.parse_package_clause();

        for _i in 0..self.tokens.len() {
            if self.peek_token().is_none() {
                return;
            }

            if self.error_mode {
                self.skip_to_next_line();
                self.error_mode = false;
                continue;
            }

            match self.peek_token().map(|t| t.kind) {
                None | Some(TokenKind::Eof) => {
                    return;
                }
                token => {
                    if self.parse_declaration() {
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

        self.resolve_names();
    }

    fn resolve_names(&mut self) {
        let errors = self
            .nodes
            .iter_mut()
            .filter(|n| n.kind == NodeKind::Identifier)
            .filter_map(|node| {
                let name = match &node.data {
                    Some(NodeData::String(s)) => s.as_str(),
                    _ => {
                        panic!("missing string node data (name) for identifier");
                    }
                };

                if let Some(_def) = self.name_to_node_def.get(name) {
                    None
                } else {
                    Some(Error::new(
                        ErrorKind::UnknownIdentifier,
                        node.origin,
                        format!("unknown identifier: {}", name),
                    ))
                }
            })
            .collect::<Vec<Error>>();

        self.errors.extend(errors);

        // Second phase: update types of identifiers.
        let idx_and_types = self
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.kind == NodeKind::Identifier && *n.typ.kind == TypeKind::Unknown)
            .map(|(i, node)| {
                let name = match &node.data {
                    Some(NodeData::String(s)) => s.as_str(),
                    _ => {
                        unreachable!()
                    }
                };

                let def_idx = *self.name_to_node_def.get(name).unwrap();
                (i, self.nodes[def_idx].typ.clone())
            })
            .collect::<Vec<_>>();
        for (idx, typ) in idx_and_types {
            self.nodes[idx].typ = typ;
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

        let mut parser = Parser::new(input, &lexer);
        parser.parse_expr();

        assert!(parser.errors.is_empty());
        let (builtins, _) = Parser::builtins(16);
        assert_eq!(parser.nodes.len(), builtins.len() + 1);

        {
            let node = &parser.nodes[builtins.len() + 0];
            assert_eq!(node.kind, NodeKind::Number);
            match node.data {
                Some(NodeData::Num(123)) => {}
                _ => panic!(),
            };
        }
    }

    #[test]
    fn parse_add() {
        let input = "123 + 45 + 0";
        let mut lexer = Lexer::new(1);
        lexer.lex(&input);

        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, &lexer);
        parser.parse_expr();

        assert!(parser.errors.is_empty());
        let (builtins, _) = Parser::builtins(16);
        assert_eq!(parser.nodes.len(), builtins.len() + 5);

        {
            let node = &parser.nodes[builtins.len() + 0];
            assert_eq!(node.kind, NodeKind::Number);
            match node.data {
                Some(NodeData::Num(123)) => {}
                _ => panic!(),
            };
        }
        {
            let node = &parser.nodes[builtins.len() + 1];
            assert_eq!(node.kind, NodeKind::Number);
            match node.data {
                Some(NodeData::Num(45)) => {}
                _ => panic!(),
            };
        }
        {
            let node = &parser.nodes[builtins.len() + 2];
            assert_eq!(node.kind, NodeKind::Add);
        }
        {
            let node = &parser.nodes[builtins.len() + 3];
            assert_eq!(node.kind, NodeKind::Number);
            match node.data {
                Some(NodeData::Num(0)) => {}
                _ => panic!(),
            };
        }
        {
            let node = &parser.nodes[builtins.len() + 4];
            assert_eq!(node.kind, NodeKind::Add);
        }
    }
}
