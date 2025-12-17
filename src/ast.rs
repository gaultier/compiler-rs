use std::num::ParseIntError;

use crate::{
    error::{Error, ErrorKind},
    lex::{Lexer, Token, TokenKind},
    origin::Origin,
    type_checker::Type,
};
use serde::Serialize;

#[derive(Serialize, Copy, Clone, PartialEq, Eq, Debug)]
pub enum NodeKind {
    Number,
    Bool,
    Add,
    Multiply,
    Divide,
    BuiltinPrintln,
    FnCall,
}

#[derive(Serialize, Copy, Clone, Debug)]
pub enum NodeData {
    Num(u64),
    Bool(bool),
}

#[derive(Serialize, Clone, Debug)]
pub struct Node {
    pub kind: NodeKind,
    pub data: Option<NodeData>,
    pub origin: Origin,
    pub typ: Type,
}

#[derive(Debug)]
pub struct Parser<'a> {
    error_mode: bool,
    pub tokens: Vec<Token>,
    tokens_consumed: usize,
    pub errors: Vec<Error>,
    pub nodes: Vec<Node>,
    input: &'a str,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str, lexer: &Lexer) -> Self {
        Self {
            error_mode: false,
            tokens: lexer.tokens.clone(),
            tokens_consumed: 0,
            errors: lexer.errors.clone(),
            nodes: Vec::new(),
            input,
        }
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
        loop {
            match self.peek_token() {
                None => return,
                Some(t) if t.kind == TokenKind::Eof || t.kind == TokenKind::Newline => {
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
            Some(t) if t.is_whitespace() => {
                self.tokens_consumed += 1;
                self.match_kind(kind)
            }
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
                typ: Type::make_int(),
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
                typ: Type::make_bool(),
            };
            self.nodes.push(node);
            return true;
        }
        if let Some(token) = self.match_kind(TokenKind::BuiltinPrintln) {
            let node = Node {
                kind: NodeKind::BuiltinPrintln,
                data: None,
                origin: token.origin,
                typ: Type::make_function(
                    &Type::make_void(),
                    &[Type::make_int()],
                    &Origin::default(),
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

        if self.match_kind(TokenKind::RightParen).is_none() {
            self.add_error_with_explanation(
                ErrorKind::ParseCallMissingRightParen,
                self.current_or_last_token_origin().unwrap(),
                String::from("missing right parenthesis after call"),
            );
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

        if self.parse_expr() {
            if self
                .match_kind1_or_kind2(TokenKind::Newline, TokenKind::Eof)
                .is_none()
            {
                let found = self.peek_token().map(|t| t.kind).unwrap_or(TokenKind::Eof);
                self.add_error_with_explanation(
                    ErrorKind::MissingNewline,
                    self.current_or_last_token_origin()
                        .unwrap_or(self.nodes.last().unwrap().origin),
                    format!(
                        "a newline is expected after a statement but found: {:?}",
                        found,
                    ),
                );
                return false;
            }
            return true;
        }

        false
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

    pub fn parse(&mut self) {
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
                None | Some(TokenKind::Eof) | Some(TokenKind::Newline) => {
                    return;
                }
                token => {
                    if self.parse_statement() {
                        continue;
                    }

                    // Catch-all.
                    self.add_error_with_explanation(
                        ErrorKind::ParseStatement,
                        self.current_or_last_token_origin().unwrap(),
                        format!(
                            "catch-all parse statement error: encountered unexpected token {:#?}",
                            token
                        ),
                    );
                }
            }
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
        parser.parse();

        assert!(parser.errors.is_empty());
        assert_eq!(parser.nodes.len(), 1);

        {
            let node = &parser.nodes[0];
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
        parser.parse();

        assert!(parser.errors.is_empty());
        assert_eq!(parser.nodes.len(), 5);

        {
            let node = &parser.nodes[0];
            assert_eq!(node.kind, NodeKind::Number);
            match node.data {
                Some(NodeData::Num(123)) => {}
                _ => panic!(),
            };
        }
        {
            let node = &parser.nodes[1];
            assert_eq!(node.kind, NodeKind::Number);
            match node.data {
                Some(NodeData::Num(45)) => {}
                _ => panic!(),
            };
        }
        {
            let node = &parser.nodes[2];
            assert_eq!(node.kind, NodeKind::Add);
        }
        {
            let node = &parser.nodes[3];
            assert_eq!(node.kind, NodeKind::Number);
            match node.data {
                Some(NodeData::Num(0)) => {}
                _ => panic!(),
            };
        }
        {
            let node = &parser.nodes[4];
            assert_eq!(node.kind, NodeKind::Add);
        }
    }
}
