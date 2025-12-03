use serde::{Deserialize, Serialize};
use std::{iter::Peekable, str::Chars};

use crate::{
    error::{Error, ErrorKind},
    origin::Origin,
};

pub struct Lexer {
    origin: Origin,
    error_mode: bool,
    pub errors: Vec<Error>,
    pub tokens: Vec<Token>,
}

#[derive(PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum TokenKind {
    Whitespace,
    LiteralNumber,
    Plus,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub origin: Origin,
}

impl Lexer {
    pub fn new() -> Self {
        Self {
            origin: Origin::new(1, 1, 0 /*, Rc::new(Vec::new())*/),
            error_mode: false,
            errors: Vec::new(),
            tokens: Vec::new(),
        }
    }

    fn add_error(&mut self, kind: ErrorKind) {
        self.errors.push(Error::new(kind, self.origin));
        self.error_mode = true;
    }

    fn lex_literal_number(&mut self, it: &mut Peekable<Chars<'_>>) {
        let start_origin = self.origin;
        let first = it.next().unwrap();
        assert!(first.is_digit(10));
        self.origin.column += 1;
        self.origin.offset += 1;

        if first == '0' {
            self.add_error(ErrorKind::InvalidLiteralNumber);
            return;
        }

        while let Some(c) = it.peek() {
            if !c.is_digit(10) {
                break;
            }

            it.next().unwrap();
            self.origin.column += 1;
            self.origin.offset += 1;
        }

        self.tokens.push(Token {
            kind: TokenKind::LiteralNumber,
            origin: start_origin,
        });
    }

    pub fn lex(&mut self, input: &str) {
        let mut it = input.chars().peekable();

        while let Some(c) = it.peek() {
            if *c != '\n' && self.error_mode {
                it.next();
                self.origin.column += 1;
                self.origin.offset += 1;
                continue;
            }
            match c {
                _ if c.is_digit(10) => self.lex_literal_number(&mut it),
                _ => self.add_error(ErrorKind::UnknownToken),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex() {
        let mut lexer = Lexer::new();
        lexer.lex("123");

        assert!(lexer.errors.is_empty());
        assert_eq!(lexer.tokens.len(), 1);

        let token = &lexer.tokens[0];
        assert_eq!(token.kind, TokenKind::LiteralNumber);
    }
}
