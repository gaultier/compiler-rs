use std::collections::BTreeMap;
use std::ffi::CStr;
use std::fs::OpenOptions;
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;

use crate::error::{Error, ErrorKind};
use crate::origin;

#[derive(Debug)]
#[repr(u32)]
enum ProgramHeaderType {
    Load = 1,
}

#[repr(u32)]
enum ProgramHeaderFlags {
    Executable = 1,
    Readable = 4,
}

#[repr(C)]
#[derive(Debug)]
struct ProgramHeader {
    typ: ProgramHeaderType,
    flags: u32,
    p_offset: u64,
    p_vaddr: u64,
    p_paddr: u64,
    p_filesz: u64,
    p_memsz: u64,
    alignment: u64,
}

#[derive(Default, Debug)]
#[repr(u32)]
enum SectionHeaderKind {
    #[default]
    Null = 0,
    Progbits = 1,
    Symtab = 2,
    Strtab = 3,
    Rela = 4,
    Hash = 5,
    Dynamic = 6,
    Note = 7,
    Nobits = 8,
    Rel = 9,
    Shlib = 10,
    Dynsym = 11,
}

#[repr(u64)]
enum SectionHeaderFlag {
    Write = 1 << 0,
    Alloc = 1 << 1,
    Execinstr = 1 << 2,
    Maskproc = 0xf000000,
}

#[derive(Default, Debug)]
#[repr(C)]
struct SectionHeader {
    name: u32,
    kind: SectionHeaderKind,
    flags: u64,
    addr: u64,
    offset: u64,
    size: u64,
    link: u32,
    info: u32,
    align: u64,
    entsize: u64,
}

fn round_up(n: usize, rnd: usize) -> usize {
    (n + (rnd - 1)) & !(rnd - 1)
}

pub fn write(asm_encoded: &[u8]) -> Result<(), Error> {
    let page_size: usize = 4 * 1024; // FIXME

    let program_headers = [ProgramHeader {
        typ: ProgramHeaderType::Load,
        flags: ProgramHeaderFlags::Executable as u32 | ProgramHeaderFlags::Readable as u32,
        p_offset: 0,
        p_vaddr: 0,
        p_paddr: 0,
        p_filesz: page_size as u64 + asm_encoded.len() as u64,
        p_memsz: page_size as u64 + asm_encoded.len() as u64,
        alignment: page_size as u64,
    }];

    let strings = [
        CStr::from_bytes_with_nul(b"\0").unwrap(),
        CStr::from_bytes_with_nul(b".shstrtab\0").unwrap(),
        CStr::from_bytes_with_nul(b".text\0").unwrap(),
        //CStr::from_bytes_with_nul(b".data\0").unwrap(),
        //CStr::from_bytes_with_nul(b".rodata\0").unwrap(),
    ];

    let mut string_indexes = BTreeMap::new();
    let mut strings_size = 0;
    {
        for s in &strings {
            string_indexes.insert(s.to_string_lossy(), strings_size as u32);
            strings_size += s.to_bytes_with_nul().len();
        }
    }
    dbg!(strings_size);

    let section_headers = [
        SectionHeader::default(), // null
        // Text (code).
        SectionHeader {
            name: *string_indexes.get(".text").unwrap() as u32,
            kind: SectionHeaderKind::Progbits,
            flags: SectionHeaderFlag::Execinstr as u64 | SectionHeaderFlag::Alloc as u64,
            addr: page_size as u64,
            offset: page_size as u64,
            size: asm_encoded.len() as u64,
            align: 16,
            ..Default::default()
        },
        // Strings.
        SectionHeader {
            name: *string_indexes.get(".shstrtab").unwrap() as u32,
            kind: SectionHeaderKind::Strtab,
            flags: 0,
            addr: 0,
            offset: page_size as u64 + round_up(asm_encoded.len(), page_size) as u64,
            size: strings_size as u64,
            align: 1,
            ..Default::default()
        },
    ];
    dbg!(&section_headers.last().unwrap());

    let mut sb = Vec::with_capacity(12 * 1024);
    {
        // Magic.
        sb.push(0x7f);
        sb.extend_from_slice(b"ELF");

        sb.push(2); // 64 bit.
        sb.push(1); // Little-endian.
        sb.push(1); // ELF header version = 1.
        sb.push(0); // OS ABI (0 = System V).

        sb.extend_from_slice(&0u64.to_le_bytes()); // Padding.
        sb.extend_from_slice(&2u16.to_le_bytes()); // Type: Executable.
        sb.extend_from_slice(&0x3eu16.to_le_bytes()); // ISA: x86_64.
        sb.extend_from_slice(&0x1u32.to_le_bytes()); // ELF: version=1.
        assert_eq!(sb.len(), 24);

        // Program entry offset.
        let program_entry_offset = program_headers[0].p_vaddr + page_size as u64;
        sb.extend_from_slice(&program_entry_offset.to_le_bytes());
        // Program header table offset.
        let elf_header_size = 64u64;
        sb.extend_from_slice(&elf_header_size.to_le_bytes());

        // Section header table offset.
        let section_header_table_offset =
            page_size as u64 + round_up(asm_encoded.len(), page_size) as u64 + strings_size as u64;
        sb.extend_from_slice(&section_header_table_offset.to_le_bytes());

        // Flags.
        sb.extend_from_slice(&0u32.to_le_bytes());

        assert_eq!(sb.len(), 52);

        // Elf header size.
        sb.extend_from_slice(&64u16.to_le_bytes());

        // Size of Program Header.
        assert_eq!(std::mem::size_of::<ProgramHeader>(), 56);
        sb.extend_from_slice(&56u16.to_le_bytes());

        // Number of entries in the program header table.
        sb.extend_from_slice(&(program_headers.len() as u16).to_le_bytes());

        // Size of Section Header.
        assert_eq!(std::mem::size_of::<SectionHeader>(), 64);
        sb.extend_from_slice(&64u16.to_le_bytes());

        // Number of entries in the program header table.
        sb.extend_from_slice(&(section_headers.len() as u16).to_le_bytes());

        // Section index in the section
        // header table.
        let section_header_string_table_index = section_headers.len() as u16 - 1;
        sb.extend_from_slice(&section_header_string_table_index.to_le_bytes());

        assert_eq!(sb.len(), 64);
    }

    for ph in &program_headers {
        let bytes = unsafe {
            std::slice::from_raw_parts(
                ph as *const ProgramHeader as *const u8,
                std::mem::size_of::<ProgramHeader>(),
            )
        };
        dbg!(ph);
        dbg!(bytes);
        sb.extend_from_slice(bytes);
    }

    // Pad.
    for _ in sb.len()..page_size {
        sb.push(0);
    }

    // Text.
    sb.extend(asm_encoded);

    // Pad.
    for _ in asm_encoded.len()..round_up(asm_encoded.len(), page_size) {
        sb.push(0);
    }

    // Strings.
    for s in &strings {
        sb.extend(s.to_bytes_with_nul());
    }

    // Section headers.
    for sh in &section_headers {
        sb.extend_from_slice(unsafe {
            std::slice::from_raw_parts(
                sh as *const SectionHeader as *const u8,
                std::mem::size_of::<SectionHeader>(),
            )
        });
    }

    let mut opts = OpenOptions::new();
    opts.create(true).write(true);
    #[cfg(unix)]
    opts.mode(0o755);

    let file_name = "hello.bin";
    let mut file = opts.open(file_name).map_err(|err| {
        Error::new(
            ErrorKind::IO,
            origin::Origin::new_unknown(),
            err.to_string(),
        )
    })?;

    file.write_all(&sb).map_err(|err| {
        Error::new(
            ErrorKind::IO,
            origin::Origin::new_unknown(),
            err.to_string(),
        )
    })
}
