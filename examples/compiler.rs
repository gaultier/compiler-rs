use std::collections::HashMap;

use compiler_rs_lib::{ast::Parser, lex::Lexer};

fn main() {
    let file_name = std::env::args().skip(1).next().unwrap();
    let file_content = std::fs::read_to_string(&file_name).unwrap();
    let mut file_id_to_names = HashMap::new();
    file_id_to_names.insert(1, file_name.clone());

    let mut lexer = Lexer::new(1);
    lexer.lex(&file_content);

    println!("--- Lex ---");
    println!("tokens: {:#?}", &lexer.tokens);

    let mut parser = Parser::new(&file_content, &lexer);
    parser.parse();

    println!("--- Parse ---");
    println!("nodes: {:#?}", &parser.nodes);
    for err in &lexer.errors {
        err.write(&mut std::io::stderr(), &file_content, &file_id_to_names)
            .unwrap();
    }
}
