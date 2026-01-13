use std::collections::HashMap;

use compiler_rs_lib::{
    asm::{self, Os},
    compile, elf,
};
use log::{LevelFilter, Log};

struct Logger {}

impl Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        eprintln!("{} {} ", record.level(), record.args());
    }

    fn flush(&self) {}
}

static LOGGER: Logger = Logger {};

fn main() {
    log::set_logger(&LOGGER)
        .map(|()| log::set_max_level(LevelFilter::Trace))
        .unwrap();

    let file_name = std::env::args().skip(1).next().unwrap();
    let file_content = std::fs::read_to_string(&file_name).unwrap();
    let mut file_id_to_name = HashMap::new();
    file_id_to_name.insert(1, file_name.clone());

    let target_arch = asm::ArchKind::Amd64;
    let os_str = std::env::args()
        .skip(2)
        .next()
        .unwrap_or_else(|| std::env::consts::OS.to_owned());

    let target_os = match os_str.as_str() {
        "linux" => Os::Linux,
        "macos" => Os::MacOS,
        x => unimplemented!("{}", x),
    };
    let compiled = compile(&file_content, 1, &file_id_to_name, target_arch);

    println!("--- Lex ---");
    println!("tokens: {:#?}", &compiled.lex_tokens);

    println!("--- Parse ---");
    println!("nodes: {:#?}", &compiled.ast_nodes);

    println!("--- Errors ---");
    for err in &compiled.errors {
        err.write(&mut std::io::stderr(), &file_content, &file_id_to_name)
            .unwrap();
        eprintln!()
    }

    println!("--- IR ---");
    println!("fn_defs: {:#?}", &compiled.ir_fn_defs);
    for fn_def in &compiled.ir_fn_defs {
        for (i, ins) in fn_def.instructions.iter().enumerate() {
            print!("{}: {}", i, ins);
        }
    }
    println!("eval: {:#?}", &compiled.ir_eval);

    //println!("--- RegAlloc ---");
    //println!("vreg_to_mem_loc: {:#?}", &compiled.vreg_to_memory_location);

    println!("--- ASM ---");
    println!("instructions: {:#?}", &compiled.asm_instructions);
    println!("{}", &compiled.asm_text);
    println!("encoded: {:x?}", &compiled.asm_encoded);

    println!("eval: {:#?}", &compiled.asm_eval);

    if !compiled.errors.is_empty() {
        std::process::exit(1)
    };

    match target_os {
        Os::Linux => elf::write_to_file("hello.bin", &compiled.asm_encoded).unwrap(),
        Os::MacOS => todo!(),
    };
}
