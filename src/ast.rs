use crate::{
    error::{Error, ErrorKind},
    lex::{Lexer, Token, TokenKind},
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

pub struct Parser<'a> {
    error_mode: bool,
    tokens: Vec<Token>,
    tokens_consumed: usize,
    errors: Vec<Error>,
    nodes: Vec<Node>,
    input: &'a str,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str, lexer: Lexer) -> Self {
        Self {
            error_mode: false,
            tokens: lexer.tokens,
            tokens_consumed: 0,
            errors: lexer.errors,
            nodes: Vec::new(),
            input,
        }
    }

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

    fn parse_primary(&mut self) -> bool {
        if self.error_mode {
            return false;
        }

        let token = &self.tokens[self.tokens_consumed];

        match token.kind {
            TokenKind::LiteralNumber => {
                self.tokens_consumed += 1;

                let src = &self.input[token.origin.offset as usize..][..token.origin.len as usize];
                let num = match u64::from_str_radix(src, 10) {
                    Ok(num) => num,
                    Err(_) => {
                        self.add_error(ErrorKind::InvalidLiteralNumber, token.origin);
                        return false;
                    }
                };
                let node = Node {
                    kind: NodeKind::Number(num),
                    origin: token.origin,
                };
                self.nodes.push(node);
                return true;
            }
            _ => {
                return false;
            }
        }
    }

    fn parse_expr(&mut self) -> bool {
        if self.error_mode {
            return false;
        }

        if self.parse_primary() {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_number() {
        let input = "123 ";
        let mut lexer = Lexer::new();
        lexer.lex(&input);

        assert!(lexer.errors.is_empty());

        let mut parser = Parser::new(input, lexer);
        parser.parse();

        assert!(parser.errors.is_empty());
        assert_eq!(parser.nodes.len(), 1);

        {
            let node = &parser.nodes[0];
            match node.kind {
                NodeKind::Number(123) => {}
                _ => assert!(false),
            };
        }
    }
}
