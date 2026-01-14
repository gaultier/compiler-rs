use std::collections::BTreeMap;
use std::ffi::CString;
use std::fs::OpenOptions;
use std::io::Write;
#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;

use log::trace;

use crate::asm::{Encoding, Visibility};

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
}

#[repr(u64)]
enum SectionHeaderFlag {
    Alloc = 1 << 1,
    Execinstr = 1 << 2,
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

#[derive(Default, Debug)]
#[repr(C)]
struct Symtab {
    name: u32, // Name (string table index).
    info: u8,  // Type and binding.
    other: u8, // Visibility.
    section_index: u16,
    value: u64,
    size: u64,
}

#[derive(Copy, Clone)]
#[repr(u8)]
enum SymbolKind {
    None = 0,
    Func = 2,
    File = 4,
}

#[derive(Copy, Clone)]
#[repr(u8)]
enum SymbolBinding {
    Local = 0,
    Global = 1,
}

impl From<Visibility> for SymbolBinding {
    fn from(value: Visibility) -> Self {
        match value {
            Visibility::Local => SymbolBinding::Local,
            Visibility::Global => SymbolBinding::Global,
        }
    }
}

fn make_symtab_info(kind: SymbolKind, binding: SymbolBinding) -> u8 {
    ((binding as u8) << 4) | ((kind as u8) & 0xf)
}

fn round_up(n: usize, rnd: usize) -> usize {
    (n + (rnd - 1)) & !(rnd - 1)
}

pub fn write<W: Write>(w: &mut W, encoding: &Encoding) -> std::io::Result<()> {
    let page_size: usize = 4 * 1024; // FIXME
    let vm_start = 1 << 22;

    let program_headers = [ProgramHeader {
        typ: ProgramHeaderType::Load,
        flags: ProgramHeaderFlags::Executable as u32 | ProgramHeaderFlags::Readable as u32,
        p_offset: 0,
        p_vaddr: vm_start,
        p_paddr: vm_start,
        p_filesz: page_size as u64 + encoding.instructions.len() as u64,
        p_memsz: page_size as u64 + encoding.instructions.len() as u64,
        alignment: page_size as u64,
    }];

    let mut strings: Vec<CString> = vec![
        c"".into(),
        c".shstrtab".into(),
        c".text".into(),
        c".symtab".into(),
        //CStr::from_bytes_with_nul(b".data\0").unwrap(),
        //CStr::from_bytes_with_nul(b".rodata\0").unwrap(),
    ];
    strings.extend(
        encoding
            .symbols
            .keys()
            .map(|s| CString::new(s.as_bytes()).unwrap()),
    );

    let mut string_indexes = BTreeMap::new();
    let mut strings_size = 0;
    {
        for s in &strings {
            string_indexes.insert(s.to_string_lossy(), strings_size as u32);
            strings_size += s.to_bytes_with_nul().len();
        }
    }

    let mut symtab = Vec::with_capacity(encoding.symbols.len() + 1);
    {
        symtab.push(Symtab::default());
        symtab.extend(encoding.symbols.iter().map(|(name, sym)| Symtab {
            name: *string_indexes.get(name.as_str()).unwrap(),
            info: make_symtab_info(SymbolKind::Func, sym.visibility.into()),
            other: 0,                                                 // TODO
            section_index: 1,                                         // .text
            value: sym.location as u64 + vm_start + page_size as u64, // Absolute position.
            size: 0,
        }));
    }
    assert_eq!(std::mem::size_of::<Symtab>(), 24);
    assert!(!symtab.is_empty());

    let section_headers = [
        SectionHeader::default(), // null
        // Text (code).
        SectionHeader {
            name: *string_indexes.get(".text").unwrap(),
            kind: SectionHeaderKind::Progbits,
            flags: SectionHeaderFlag::Execinstr as u64 | SectionHeaderFlag::Alloc as u64,
            addr: vm_start + page_size as u64,
            offset: page_size as u64,
            size: encoding.instructions.len() as u64,
            align: 16,
            ..Default::default()
        },
        // Strings.
        SectionHeader {
            name: *string_indexes.get(".shstrtab").unwrap(),
            kind: SectionHeaderKind::Strtab,
            flags: 0,
            addr: 0,
            offset: page_size as u64 + round_up(encoding.instructions.len(), page_size) as u64,
            size: strings_size as u64,
            align: 1,
            ..Default::default()
        },
        // Symtab.
        SectionHeader {
            name: *string_indexes.get(".symtab").unwrap(),
            kind: SectionHeaderKind::Symtab,
            flags: 0,
            addr: 0,
            offset: page_size as u64
                + round_up(encoding.instructions.len(), page_size) as u64
                + strings_size as u64,
            size: (symtab.len() * std::mem::size_of::<Symtab>()) as u64,
            align: std::mem::align_of::<Symtab>() as u64,
            entsize: std::mem::size_of::<Symtab>() as u64,
            link: 2, // strings
            info: symtab.len() as u32,
        },
    ];

    {
        // Magic.
        w.write_all(&[0x7f])?;
        w.write_all(b"ELF")?;

        w.write_all(&[2])?; // 64 bit.
        w.write_all(&[1])?; // Little-endian.
        w.write_all(&[1])?; // ELF header version = 1.
        w.write_all(&[0])?; // OS ABI (0 = System V).

        w.write_all(&0u64.to_le_bytes())?; // Padding.
        w.write_all(&2u16.to_le_bytes())?; // Type: Executable.
        w.write_all(&0x3eu16.to_le_bytes())?; // ISA: x86_64.
        w.write_all(&0x1u32.to_le_bytes())?; // ELF: version=1.

        // Program entry offset.
        let program_entry_offset =
            program_headers[0].p_vaddr + page_size as u64 + encoding.entrypoint as u64;
        w.write_all(&program_entry_offset.to_le_bytes())?;
        // Program header table offset.
        let elf_header_size = 64u64;
        w.write_all(&elf_header_size.to_le_bytes())?;

        // Section header table offset.
        let section_header_table_offset = page_size as u64
            + round_up(encoding.instructions.len(), page_size) as u64
            + strings_size as u64
            + (symtab.len() * std::mem::size_of::<Symtab>()) as u64;
        w.write_all(&section_header_table_offset.to_le_bytes())?;

        // Flags.
        w.write_all(&0u32.to_le_bytes())?;

        // Elf header size.
        w.write_all(&64u16.to_le_bytes())?;

        // Size of Program Header.
        assert_eq!(std::mem::size_of::<ProgramHeader>(), 56);
        w.write_all(&56u16.to_le_bytes())?;

        // Number of entries in the program header table.
        w.write_all(&(program_headers.len() as u16).to_le_bytes())?;

        // Size of Section Header.
        assert_eq!(std::mem::size_of::<SectionHeader>(), 64);
        w.write_all(&64u16.to_le_bytes())?;

        // Number of entries in the program header table.
        w.write_all(&(section_headers.len() as u16).to_le_bytes())?;

        // Section index in the section
        // header table.
        let section_header_string_table_index = 2u16;
        w.write_all(&section_header_string_table_index.to_le_bytes())?;
    }
    let mut written = 64;

    for ph in &program_headers {
        let bytes = unsafe {
            std::slice::from_raw_parts(
                ph as *const ProgramHeader as *const u8,
                std::mem::size_of::<ProgramHeader>(),
            )
        };
        w.write_all(bytes)?;
        written += bytes.len();
    }

    // Pad.
    for _ in written..page_size {
        w.write_all(&[0])?;
    }

    // Text.
    w.write_all(&encoding.instructions)?;

    // Pad.
    for _ in encoding.instructions.len()..round_up(encoding.instructions.len(), page_size) {
        w.write_all(&[0])?;
    }

    // Strings.
    for s in &strings {
        w.write_all(s.to_bytes_with_nul())?;
    }

    for s in &symtab {
        w.write_all(unsafe {
            std::slice::from_raw_parts(
                s as *const Symtab as *const u8,
                std::mem::size_of::<Symtab>(),
            )
        })?;
    }

    // Section headers.
    for sh in &section_headers {
        w.write_all(unsafe {
            std::slice::from_raw_parts(
                sh as *const SectionHeader as *const u8,
                std::mem::size_of::<SectionHeader>(),
            )
        })?;
    }

    w.flush()
}

pub fn write_to_file(file_name: &str, encoding: &Encoding) -> std::io::Result<()> {
    let mut opts = OpenOptions::new();
    opts.create(true).write(true);
    #[cfg(unix)]
    opts.mode(0o755);

    let mut file = opts.open(file_name)?;
    trace!("elf: action=write file={}", file_name);

    write(&mut file, encoding)
}
