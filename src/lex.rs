use miniserde::{Deserialize, Serialize};
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

#[derive(PartialEq, Eq, Debug, Serialize, Deserialize, Copy, Clone)]
pub enum TokenKind {
    Whitespace,
    LiteralNumber,
    Plus,
    Eof,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub origin: Origin,
}

impl Lexer {
    pub fn new() -> Self {
        Self {
            origin: Origin::new(1, 1, 0, 0 /*, Rc::new(Vec::new())*/),
            error_mode: false,
            errors: Vec::new(),
            tokens: Vec::new(),
        }
    }

    fn add_error(&mut self, kind: ErrorKind, len: u32) {
        let origin = Origin { len, ..self.origin };
        self.errors.push(Error::new(kind, origin, String::new()));
        self.error_mode = true;
    }

    fn add_error_at(&mut self, kind: ErrorKind, origin: Origin) {
        self.errors.push(Error::new(kind, origin, String::new()));
        self.error_mode = true;
    }

    fn lex_literal_number(&mut self, it: &mut Peekable<Chars<'_>>) {
        let start_origin = self.origin;
        let first = it.next().unwrap();
        assert!(first.is_ascii_digit());
        self.origin.column += 1;
        self.origin.offset += 1;

        while let Some(c) = it.peek() {
            if !c.is_ascii_digit() {
                break;
            }

            self.origin.column += 1;
            self.origin.offset += 1;
            it.next();
        }

        let len = self.origin.offset - start_origin.offset;
        let origin = Origin {
            len,
            ..start_origin
        };

        if first == '0' {
            self.add_error_at(ErrorKind::InvalidLiteralNumber, origin);
            return;
        }

        self.tokens.push(Token {
            kind: TokenKind::LiteralNumber,
            origin,
        });
    }

    pub fn lex(&mut self, input: &str) {
        let mut it = input.chars().peekable();

        while let Some(c) = it.peek() {
            let c = *c;
            if c != '\n' && self.error_mode {
                self.origin.column += 1;
                self.origin.offset += 1;
                it.next();
                continue;
            }
            match c {
                '+' => {
                    let origin = Origin {
                        len: 1,
                        ..self.origin
                    };
                    self.tokens.push(Token {
                        kind: TokenKind::Plus,
                        origin,
                    });
                    self.origin.offset += 1;
                    self.origin.column += 1;
                    it.next();
                }
                _ if c.is_whitespace() => {
                    self.origin.offset += 1;

                    if c == '\n' {
                        self.origin.column = 1;
                        self.origin.line += 1;
                    } else {
                        self.origin.column += 1;
                    }
                    it.next();
                }
                _ if c.is_ascii_digit() => self.lex_literal_number(&mut it),
                _ => {
                    self.add_error(ErrorKind::UnknownToken, 1);
                    self.origin.column += 1;
                    self.origin.offset += 1;
                    it.next();
                }
            }
        }
        let origin = Origin {
            len: 0,
            ..self.origin
        };
        self.tokens.push(Token {
            kind: TokenKind::Eof,
            origin,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_number() {
        let mut lexer = Lexer::new();
        lexer.lex("123 4567\n 01");

        assert_eq!(lexer.errors.len(), 1);
        assert_eq!(lexer.tokens.len(), 3);

        {
            let token = &lexer.tokens[0];
            assert_eq!(token.kind, TokenKind::LiteralNumber);
            assert_eq!(token.origin.offset, 0);
            assert_eq!(token.origin.line, 1);
            assert_eq!(token.origin.column, 1);
            assert_eq!(token.origin.len, 3);
        }
        {
            let token = &lexer.tokens[1];
            assert_eq!(token.kind, TokenKind::LiteralNumber);
            assert_eq!(token.origin.offset, 4);
            assert_eq!(token.origin.line, 1);
            assert_eq!(token.origin.column, 5);
            assert_eq!(token.origin.len, 4);
        }
        {
            let token = &lexer.tokens[2];
            assert_eq!(token.kind, TokenKind::Eof);
        }
        {
            let err = &lexer.errors[0];
            assert_eq!(err.kind, ErrorKind::InvalidLiteralNumber);
            assert_eq!(err.origin.offset, 10);
            assert_eq!(err.origin.line, 2);
            assert_eq!(err.origin.column, 2);
            assert_eq!(err.origin.len, 2);
        }
    }

    #[test]
    fn lex_unknown() {
        let mut lexer = Lexer::new();
        lexer.lex(" &");

        assert_eq!(lexer.tokens.len(), 1);
        assert_eq!(lexer.errors.len(), 1);

        let token = &lexer.tokens[0];
        assert_eq!(token.kind, TokenKind::Eof);

        let err = &lexer.errors[0];
        assert_eq!(err.kind, ErrorKind::UnknownToken);
        assert_eq!(err.origin.offset, 1);
        assert_eq!(err.origin.line, 1);
        assert_eq!(err.origin.column, 2);
        assert_eq!(err.origin.len, 1);
    }
}
