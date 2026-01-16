use std::collections::{BTreeMap, HashMap};

use compiler_rs_lib::{
    asm::{self, Encoding, Os},
    compile, elf, macho,
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

    println!("--- Errors: {} ---", compiled.errors.len());
    for err in &compiled.errors {
        err.write(&mut std::io::stderr(), &file_content, &file_id_to_name)
            .unwrap();
        eprintln!()
    }

    //println!("--- RegAlloc ---");
    //println!("vreg_to_mem_loc: {:#?}", &compiled.vreg_to_memory_location);

    if !compiled.errors.is_empty() {
        std::process::exit(1)
    };

    let output_file_name = "hello.bin"; // FIXME
    match target_os {
        Os::Linux => elf::write_to_file(output_file_name, &compiled.asm_encoded).unwrap(),
        Os::MacOS => {
            // FIXME
            let encoding = Encoding {
                instructions: vec![
                    0x48, 0xc7, 0xc0, 0x01, 0x00, 0x00, 0x02, // mov rax, 0x2000001
                    0x48, 0xc7, 0xc7, 0x02, 0x00, 0x00, 0x00, // mov rdi, 2
                    0x0f, 0x05, // syscall
                ],
                entrypoint: 0,
                symbols: BTreeMap::new(),
            };
            macho::write_to_file(output_file_name, &encoding).unwrap();
        }
    };
}
