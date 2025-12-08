use std::{collections::HashMap, io::stdout};

use compiler_rs_lib::{ast::Parser, ir, lex::Lexer};

fn main() {
    let file_name = std::env::args().skip(1).next().unwrap();
    let file_content = std::fs::read_to_string(&file_name).unwrap();
    let mut file_id_to_names = HashMap::new();
    file_id_to_names.insert(1, file_name.clone());

    println!("--- Lex ---");
    let mut lexer = Lexer::new(1);
    lexer.lex(&file_content);
    println!("tokens: {:#?}", &lexer.tokens);

    println!("--- Parse ---");
    let mut parser = Parser::new(&file_content, &lexer);
    parser.parse();
    println!("nodes: {:#?}", &parser.nodes);
    for err in &parser.errors {
        err.write(&mut std::io::stderr(), &file_content, &file_id_to_names)
            .unwrap();
    }

    let mut ir_emitter = ir::Emitter::new();
    ir_emitter.emit(&parser.nodes);
    println!("--- IR ---");
    println!("instructions: {:#?}", &ir_emitter.instructions);
    for ins in &ir_emitter.instructions {
        ins.write(&mut stdout()).unwrap();
    }

    std::process::exit(if parser.errors.is_empty() { 0 } else { 1 });
}
