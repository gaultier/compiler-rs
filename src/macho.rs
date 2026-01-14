#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;
use std::{fs::OpenOptions, io::Write};

use log::trace;

use crate::asm::Encoding;

#[repr(u32)]
enum CpuKind {
    X86 = 0x7,
    Arm = 0xc,
}

#[repr(u32)]
enum CpuSubKindX86 {
    All = 0x3,
}

#[repr(u32)]
enum FileKind {
    DemandPagedExecutable = 0x2,
}

#[repr(C)]
struct Header {
    magic: u32,
    cpu_kind: CpuKind,
    cpu_subkind: u32,
    file_kind: FileKind,
    cmds_count: u32,
    cmds_bytes_count: u32,
    flags: u32,
    reserved: u32,
}

#[repr(C)]
struct Section64 {
    sect_name: [u8; 16],
    seg_name: [u8; 16],
    addr: u64,
    size: u64,
    offset: u32,
    align: u32,
    reloff: u32,
    nreloc: u32,
    flags: u32,
    reserved: [u32; 3],
}

#[repr(u32)]
enum LoadCommandKind {
    Symtab = 0x2,
    Segment64 = 0x19,
}

#[repr(C)]
struct LoadCommand {
    cmd: LoadCommandKind,
    cmd_size: u32,
}

#[repr(u32)]
enum MachoFlags {
    NoUndefinedReferences = (1 << 0),
    Pie = (1 << 21),
}

pub fn write<W: Write>(w: &mut W, encoding: &Encoding) -> std::io::Result<()> {
    assert_eq!(std::mem::size_of::<Header>(), 32);
    assert_eq!(std::mem::size_of::<Section64>(), 80);
    assert_eq!(std::mem::size_of::<LoadCommand>(), 8);

    let cmds_count = 0; // TODO
    let cmds_bytes_count = 0; // TODO
    let header = Header {
        magic: 0xfe_ed_fa_cf, // 64 bits.
        cpu_kind: CpuKind::X86,
        cpu_subkind: CpuSubKindX86::All as u32,
        file_kind: FileKind::DemandPagedExecutable,
        cmds_count,
        cmds_bytes_count,
        flags: MachoFlags::NoUndefinedReferences as u32 | MachoFlags::Pie as u32,
        reserved: 0,
    };

    let bytes = unsafe {
        std::slice::from_raw_parts(
            &header as *const Header as *const u8,
            std::mem::size_of::<Header>(),
        )
    };
    w.write_all(bytes)?;

    w.flush()
}

pub fn write_to_file(file_name: &str, encoding: &Encoding) -> std::io::Result<()> {
    let mut opts = OpenOptions::new();
    opts.create(true).write(true);
    #[cfg(unix)]
    opts.mode(0o755);

    let mut file = opts.open(file_name)?;
    trace!("macho: action=write file={}", file_name);

    write(&mut file, encoding)
}
