use wasm_bindgen::JsValue;
use wasm_bindgen::prelude::wasm_bindgen;

use crate::lex::Lexer;

pub mod error;
pub mod lex;
mod origin;

#[wasm_bindgen]
pub fn lex(input: &str) -> JsValue {
    let mut lexer = Lexer::new();
    lexer.lex(input);
    serde_wasm_bindgen::to_value(&(lexer.tokens.as_slice(), lexer.errors.as_slice())).unwrap()
}
