use crate::{
    lex::{Token, TokenKind},
    origin::Origin,
};

pub enum NodeKind {
    Number(u64),
    Add,
}

pub struct Node {
    kind: NodeKind,
    origin: Origin,
}

pub struct Parser {
    error_mode: bool,
    tokens: Vec<Token>,
    tokens_consumed: usize,
}

impl Parser {
    fn parse_expr(&mut self) -> bool {}

    pub fn emit(&mut self) {
        for _i in 0..self.tokens.len() {
            assert!(self.tokens_consumed <= self.tokens.len());
            if self.tokens_consumed == self.tokens.len() {
                return;
            }

            let kind = self.tokens[self.tokens_consumed].kind;
            match kind {
                TokenKind::Eof => {
                    return;
                }
                // TODO: err mode skip.
                _ => {
                    if self.parse_expr() {
                        continue;
                    }
                }
            }
        }
    }
}
