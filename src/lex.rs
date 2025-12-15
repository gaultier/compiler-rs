use serde::Serialize;
use std::{iter::Peekable, str::Chars};

use crate::{
    error::{Error, ErrorKind},
    origin::{FileId, Origin},
};

#[derive(Debug)]
pub struct Lexer {
    origin: Origin,
    error_mode: bool,
    pub errors: Vec<Error>,
    pub tokens: Vec<Token>,
}

#[derive(PartialEq, Eq, Debug, Serialize, Copy, Clone)]
pub enum TokenKind {
    Whitespace,
    LiteralNumber,
    LiteralBool,
    Identifier,
    BuiltinPrintln,
    Plus,
    Star,
    Slash,
    Newline,
    LeftParen,
    RightParen,
    Eof,
    Unknown,
}

#[derive(Serialize, Debug, Copy, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub origin: Origin,
}

impl Lexer {
    pub fn new(file_id: FileId) -> Self {
        Self {
            origin: Origin::new(1, 1, 0, 0, file_id),
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

    fn lex_keyword(&mut self, input: &str, it: &mut Peekable<Chars<'_>>) {
        let start_origin = self.origin;
        let first = it.next().unwrap();
        assert!(first.is_ascii_alphabetic());
        self.origin.column += 1;
        self.origin.offset += 1;

        while let Some(c) = it.peek() {
            if !(c.is_alphanumeric() || *c == '_') {
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

        let lit = &input[origin.offset as usize..origin.offset as usize + len as usize];
        let kind = match lit {
            "true" | "false" => TokenKind::LiteralBool,
            "println" => TokenKind::BuiltinPrintln,
            _ => TokenKind::Identifier,
        };

        self.tokens.push(Token { kind, origin });
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

        if first == '0' && len > 1 {
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
                '\n' => {
                    let origin = Origin {
                        len: 1,
                        ..self.origin
                    };
                    self.tokens.push(Token {
                        kind: TokenKind::Newline,
                        origin,
                    });
                    self.origin.offset += 1;
                    self.origin.column = 1;
                    self.origin.line += 1;
                    it.next();
                }
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
                '*' => {
                    let origin = Origin {
                        len: 1,
                        ..self.origin
                    };
                    self.tokens.push(Token {
                        kind: TokenKind::Star,
                        origin,
                    });
                    self.origin.offset += 1;
                    self.origin.column += 1;
                    it.next();
                }
                '/' => {
                    let origin = Origin {
                        len: 1,
                        ..self.origin
                    };
                    self.tokens.push(Token {
                        kind: TokenKind::Slash,
                        origin,
                    });
                    self.origin.offset += 1;
                    self.origin.column += 1;
                    it.next();
                }
                '(' => {
                    let origin = Origin {
                        len: 1,
                        ..self.origin
                    };
                    self.tokens.push(Token {
                        kind: TokenKind::LeftParen,
                        origin,
                    });
                    self.origin.offset += 1;
                    self.origin.column += 1;
                    it.next();
                }
                ')' => {
                    let origin = Origin {
                        len: 1,
                        ..self.origin
                    };
                    self.tokens.push(Token {
                        kind: TokenKind::RightParen,
                        origin,
                    });
                    self.origin.offset += 1;
                    self.origin.column += 1;
                    it.next();
                }
                _ if c.is_whitespace() => {
                    self.origin.offset += 1;

                    self.origin.column += 1;
                    it.next();
                }
                _ if c.is_ascii_digit() => self.lex_literal_number(&mut it),
                _ if c.is_ascii_alphabetic() => self.lex_keyword(input, &mut it),
                _ => {
                    self.tokens.push(Token {
                        kind: TokenKind::Unknown,
                        origin: Origin {
                            len: 1,
                            ..self.origin
                        },
                    });

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

impl Token {
    pub(crate) fn is_whitespace(&self) -> bool {
        self.kind == TokenKind::Whitespace || self.kind == TokenKind::Newline
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_number() {
        let mut lexer = Lexer::new(0);
        lexer.lex("123 4567\n 01");

        assert_eq!(lexer.errors.len(), 1);
        assert_eq!(lexer.tokens.len(), 4);

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
            assert_eq!(token.kind, TokenKind::Newline);
            assert_eq!(token.origin.offset, 8);
            assert_eq!(token.origin.line, 1);
            assert_eq!(token.origin.column, 9);
            assert_eq!(token.origin.len, 1);
        }
        {
            let token = &lexer.tokens[3];
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
        let mut lexer = Lexer::new(0);
        lexer.lex(" &");

        assert_eq!(lexer.tokens.len(), 2);
        assert_eq!(lexer.errors.len(), 1);

        {
            let token = &lexer.tokens[0];
            assert_eq!(token.kind, TokenKind::Unknown);
        }
        {
            let token = &lexer.tokens[1];
            assert_eq!(token.kind, TokenKind::Eof);
        }

        let err = &lexer.errors[0];
        assert_eq!(err.kind, ErrorKind::UnknownToken);
        assert_eq!(err.origin.offset, 1);
        assert_eq!(err.origin.line, 1);
        assert_eq!(err.origin.column, 2);
        assert_eq!(err.origin.len, 1);
    }
}
