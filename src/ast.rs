use crate::{
    error::{Error, ErrorKind},
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
    errors: Vec<Error>,
}

impl Parser {
    fn advance_to_next_line_from_last_error(&mut self) {
        assert!(self.tokens_consumed <= self.tokens.len());
        if self.tokens_consumed == self.tokens.len() {
            // Already at EOF.
            return;
        }

        let last_error = self.errors.last().unwrap();
        let line = self.tokens[self.tokens_consumed].origin.line;
        if line > last_error.origin.line {
            // No-op.
            return;
        }

        while self.tokens_consumed < self.tokens.len() {
            let token_line = self.tokens[self.tokens_consumed].origin.line;
            if token_line > line {
                break;
            }

            self.tokens_consumed += 1;
        }
    }

    fn add_error(&mut self, kind: ErrorKind, origin: Origin) {
        if self.error_mode {
            return;
        }

        self.errors
            .push(Error::new(kind, origin, String::default()));
        self.error_mode = true;

        // Skip to the next newline to avoid having cascading errors.
        self.advance_to_next_line_from_last_error();
    }

    fn parse_expr(&mut self) -> bool {
        if self.error_mode {
            return false;
        }

        // TODO

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

    pub fn emit(&mut self) {
        for _i in 0..self.tokens.len() {
            assert!(self.tokens_consumed <= self.tokens.len());
            if self.tokens_consumed == self.tokens.len() {
                // EOF.
                return;
            }

            if self.error_mode {
                self.advance_to_next_line_from_last_error();
                self.error_mode = false;
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

                    // Catch-all.
                    self.add_error(
                        ErrorKind::ParseStatement,
                        self.current_or_last_token_origin().unwrap(),
                    );
                }
            }
        }
    }
}
