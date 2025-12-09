use std::{collections::HashMap, io::stdout};

use compiler_rs_lib::{
    asm::{self, amd64},
    ast::Parser,
    ir,
    lex::Lexer,
    register_alloc,
};

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
    println!("lifetimes: {:#?}", &ir_emitter.lifetimes);
    for (i, ins) in ir_emitter.instructions.iter().enumerate() {
        print!("{}: ", i);
        ins.write(&mut stdout()).unwrap();
    }
    let interpreted = ir::interpret(&ir_emitter.instructions);
    println!("interpreted: {:#?}", &interpreted);

    println!("--- RegAlloc ---");
    let regalloc = register_alloc::regalloc(&ir_emitter.lifetimes, &amd64::abi());
    println!("regalloc: {:#?}", &regalloc);

    let mut asm_emitter = asm::amd64::Emitter::new();
    asm_emitter.emit(&ir_emitter.instructions, &regalloc);
    println!("--- ASM ---");
    println!("instructions: {:#?}", &asm_emitter.instructions);
    for (i, ins) in asm_emitter.instructions.iter().enumerate() {
        print!("{}: ", i);
        ins.write(&mut stdout()).unwrap();
    }

    std::process::exit(if parser.errors.is_empty() { 0 } else { 1 });
}
