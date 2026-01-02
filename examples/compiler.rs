use std::{
    collections::HashMap,
    io::{Write, stdout},
};

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
    let mut file_id_to_names = HashMap::new();
    file_id_to_names.insert(1, file_name.clone());

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
    let compiled = compile(&file_content, 1, target_arch);

    println!("--- Lex ---");
    println!("tokens: {:#?}", &compiled.lex_tokens);

    println!("--- Parse ---");
    println!("nodes: {:#?}", &compiled.ast_nodes);

    println!("--- Errors ---");
    for err in &compiled.errors {
        err.write(&mut std::io::stderr(), &file_content, &file_id_to_names)
            .unwrap();
        std::io::stderr().write_all(b"\n").unwrap();
    }

    println!("--- IR ---");
    println!("instructions: {:#?}", &compiled.ir_instructions);
    println!("live_ranges: {:#?}", &compiled.ir_live_ranges);
    for (i, ins) in compiled.ir_instructions.iter().enumerate() {
        print!("{}: ", i);
        ins.write(&mut stdout()).unwrap();
    }
    println!("eval: {:#?}", &compiled.ir_eval);

    println!("--- RegAlloc ---");
    println!("vreg_to_mem_loc: {:#?}", &compiled.vreg_to_memory_location);

    println!("--- ASM ---");
    println!("instructions: {:#?}", &compiled.asm_instructions);
    for (i, ins) in compiled.asm_instructions.iter().enumerate() {
        println!("{}: {}", i, ins);
    }
    println!("encoded: {:x?}", &compiled.asm_encoded);

    println!("eval: {:#?}", &compiled.asm_eval);

    if !compiled.errors.is_empty() {
        std::process::exit(1)
    };

    let dummy_asm = &[0xb8, 0x3c, 0, 0, 0, 0xba, 0, 0, 0, 0, 0x0f, 0x05];

    match target_os {
        Os::Linux => elf::write(dummy_asm).unwrap(),
        Os::MacOS => todo!(),
    };
}
