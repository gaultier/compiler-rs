#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;
use std::{fs::OpenOptions, io::Write};

use log::trace;

use crate::{asm::Encoding, utils};

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
    cpu_kind: u32, // CpuKind + 1 bit set for 64 bits.
    cpu_subkind: u32,
    file_kind: FileKind,
    cmds_count: u32,
    cmds_bytes_count: u32,
    flags: u32,
    reserved: u32,
}

#[repr(C)]
struct SegmentLoad64 {
    name: [u8; 16],
    vm_addr: u64,
    vm_size: u64,
    file_offset: u64,
    file_size: u64,
    max_vmem_protect: u32,
    init_vmem_protect: u32,
    sections_count: u32,
    flags: u32,
}

#[repr(u32)]
enum LoadCommandKind {
    Symtab = 0x2,
    Segment64 = 0x19,
}

#[repr(u32)]
enum Permissions {
    Read = 0b01,
    Write = 0b10,
    Exec = 0b100,
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
    assert_eq!(std::mem::size_of::<SegmentLoad64>(), 64);
    assert_eq!(std::mem::size_of::<LoadCommand>(), 8);

    let page_size = 4 * 1024; // TODO: On ARM: 16KiB.
    let cmds = [
        SegmentLoad64 {
            name: *b"__PAGEZERO\0\0\0\0\0\0",
            vm_addr: 0,
            vm_size: u32::MAX as u64,
            file_offset: 0,
            file_size: 0,
            max_vmem_protect: 0,
            init_vmem_protect: 0,
            sections_count: 0,
            flags: 0,
        },
        SegmentLoad64 {
            name: *b"__TEXT\0\0\0\0\0\0\0\0\0\0",
            vm_addr: u32::MAX as u64 + 1,
            vm_size: utils::round_up(encoding.instructions.len(), page_size) as u64,
            file_offset: 0,
            file_size: utils::round_up(encoding.instructions.len(), page_size) as u64,
            max_vmem_protect: Permissions::Read as u32 | Permissions::Exec as u32,
            init_vmem_protect: Permissions::Read as u32 | Permissions::Exec as u32,
            sections_count: 0, // TODO: 1.
            flags: 0,
        },
    ];
    let cmds_bytes_count = ((std::mem::size_of::<LoadCommand>()
        + std::mem::size_of::<SegmentLoad64>()) // FIXME: variable size.
        * cmds.len()) as u32;

    let header = Header {
        magic: 0xfe_ed_fa_cf,                       // 64 bits.
        cpu_kind: CpuKind::X86 as u32 | 0x01000000, // 64 bits.
        cpu_subkind: CpuSubKindX86::All as u32,
        file_kind: FileKind::DemandPagedExecutable,
        cmds_count: cmds.len() as u32,
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

    for cmd in &cmds {
        let cmd_kind = 0x19u32; // SegmentLoad64.
        let cmd_size =
            (std::mem::size_of::<LoadCommand>() + std::mem::size_of::<SegmentLoad64>()) as u32;

        w.write_all(&cmd_kind.to_le_bytes())?;
        w.write_all(&cmd_size.to_le_bytes())?;

        let bytes = unsafe {
            std::slice::from_raw_parts(
                cmd as *const SegmentLoad64 as *const u8,
                std::mem::size_of::<SegmentLoad64>(),
            )
        };
        w.write_all(bytes)?;
    }

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
