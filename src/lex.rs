pub struct Lexer {
    line: u32,
    column: u32,
    err_mode: bool,
}

pub enum TokenKind {
    Whitespace,
    LiteralNumber,
    Plus,
}

pub struct Token {
    kind: TokenKind,
}

impl Lexer {
    pub fn new() -> Self {
        Self {
            line: 1,
            column: 1,
            err_mode: false,
        }
    }

    pub fn lex(&mut self, input: String) {}
}
