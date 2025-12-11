use std::{collections::HashMap, io::stdout};

use compiler_rs_lib::{asm, compile};

fn main() {
    let file_name = std::env::args().skip(1).next().unwrap();
    let file_content = std::fs::read_to_string(&file_name).unwrap();
    let mut file_id_to_names = HashMap::new();
    file_id_to_names.insert(1, file_name.clone());

    let compiled = compile(&file_content, 1, asm::ArchKind::Amd64);

    println!("--- Lex ---");
    println!("tokens: {:#?}", &compiled.lex_tokens);

    println!("--- Parse ---");
    println!("nodes: {:#?}", &compiled.ast_nodes);
    for err in &compiled.errors {
        err.write(&mut std::io::stderr(), &file_content, &file_id_to_names)
            .unwrap();
    }

    println!("--- IR ---");
    println!("instructions: {:#?}", &compiled.ir_instructions);
    println!("live_ranges: {:#?}", &compiled.ir_live_ranges);
    for (i, ins) in compiled.ir_instructions.iter().enumerate() {
        print!("{}: ", i);
        ins.write(&mut stdout()).unwrap();
    }
    println!("eval: {:#?}", &compiled.ir_eval);

    println!("--- VCode ---");
    println!("vcode: {:#?}", &compiled.vcode);
    for (i, ins) in compiled.vcode.iter().enumerate() {
        print!("{}: ", i);
        ins.write(&mut stdout()).unwrap();
    }

    println!("--- RegAlloc ---");
    println!("vreg_to_mem_loc: {:#?}", &compiled.vreg_to_memory_location);

    println!("--- ASM ---");
    println!("instructions: {:#?}", &compiled.asm_instructions);
    for (i, ins) in compiled.asm_instructions.iter().enumerate() {
        print!("{}: ", i);
        ins.write(&mut stdout()).unwrap();
    }

    println!("eval: {:#?}", &compiled.asm_eval);

    std::process::exit(if compiled.errors.is_empty() { 0 } else { 1 });
}
