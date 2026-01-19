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

enum LoadCommand {
    SegmentLoad(SegmentLoad),
    UnixThread(UnixThread),
}

struct UnixThread {
    // TODO
}

struct SegmentLoad {
    name: [u8; 16],
    vm_addr: u64,
    vm_size: u64,
    file_offset: u64,
    file_size: u64,
    max_vmem_protect: u32,
    init_vmem_protect: u32,
    flags: u32,
    sections: Vec<Section>,
}

#[repr(u32)]
enum SectionFlag {
    OnlyContainsTrueMachineInstructions = 0x80000000,
    ContainsSomeMachineInstructions = 0x400,
}

struct Section {
    section_name: [u8; 16],
    segment_name: [u8; 16],
    section_addr: u64,
    section_size: u64,
    section_file_offset: u32,
    alignment: u32,
    relocations_file_offset: u32,
    relocations_count: u32,
    flags: u32,
    typ: u8,
    reserved: [u32; 3],
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

#[repr(u32)]
enum MachoFlags {
    NoUndefinedReferences = (1 << 0),
    Pie = (1 << 21),
}

impl LoadCommand {
    fn bin_size(&self) -> usize {
        match self {
            LoadCommand::SegmentLoad(x) => x.bin_size(),
            LoadCommand::UnixThread(x) => x.bin_size(),
        }
    }

    fn as_segment_load(&self) -> Option<&SegmentLoad> {
        match self {
            LoadCommand::SegmentLoad(x) => Some(x),
            _ => None,
        }
    }

    fn as_segment_load_mut(&mut self) -> Option<&mut SegmentLoad> {
        match self {
            LoadCommand::SegmentLoad(x) => Some(x),
            _ => None,
        }
    }

    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self {
            LoadCommand::SegmentLoad(x) => x.write(w),
            LoadCommand::UnixThread(x) => x.write(w),
        }
    }
}

impl UnixThread {
    fn bin_size(&self) -> usize {
        todo!()
    }

    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        todo!()
    }
}

impl SegmentLoad {
    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        let cmd_kind = 0x19u32; // SegmentLoad64.
        let cmd_size: u32 = self.bin_size() as u32;

        w.write_all(&cmd_kind.to_le_bytes())?;
        w.write_all(&cmd_size.to_le_bytes())?;

        w.write_all(&self.name)?;
        w.write_all(&self.vm_addr.to_le_bytes())?;
        w.write_all(&self.vm_size.to_le_bytes())?;
        w.write_all(&self.file_offset.to_le_bytes())?;
        w.write_all(&self.file_size.to_le_bytes())?;
        w.write_all(&self.max_vmem_protect.to_le_bytes())?;
        w.write_all(&self.init_vmem_protect.to_le_bytes())?;
        w.write_all(&(self.sections.len() as u32).to_le_bytes())?;
        w.write_all(&self.flags.to_le_bytes())?;

        for sec in &self.sections {
            sec.write(w)?;
        }

        Ok(())
    }

    fn bin_size(&self) -> usize {
        72usize
            + self
                .sections
                .iter()
                .map(|x: &Section| x.bin_size())
                .sum::<usize>()
    }
}

impl Section {
    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(&self.section_name)?;
        w.write_all(&self.segment_name)?;
        w.write_all(&self.section_addr.to_le_bytes())?;
        w.write_all(&self.section_size.to_le_bytes())?;
        w.write_all(&self.section_file_offset.to_le_bytes())?;
        w.write_all(&self.alignment.to_le_bytes())?;
        w.write_all(&self.relocations_file_offset.to_le_bytes())?;
        w.write_all(&self.relocations_count.to_le_bytes())?;

        let flags_typ = self.flags << 8 | (self.typ as u32);
        w.write_all(&flags_typ.to_le_bytes())?;
        for r in &self.reserved {
            w.write_all(&r.to_le_bytes())?;
        }

        Ok(())
    }

    fn bin_size(&self) -> usize {
        80
    }
}

pub fn write<W: Write>(w: &mut W, encoding: &Encoding) -> std::io::Result<()> {
    assert_eq!(std::mem::size_of::<Header>(), 32);

    let page_size = 4 * 1024; // TODO: On ARM: 16KiB.
    let text_start = 1u64 << 32;
    let mut cmds = [
        LoadCommand::SegmentLoad(SegmentLoad {
            name: *b"__PAGEZERO\0\0\0\0\0\0",
            vm_addr: 0,
            vm_size: text_start,
            file_offset: 0,
            file_size: 0,
            max_vmem_protect: 0,
            init_vmem_protect: 0,
            flags: 0,
            sections: Vec::new(),
        }),
        LoadCommand::UnixThread(UnixThread {}),
        LoadCommand::SegmentLoad(SegmentLoad {
            name: *b"__TEXT\0\0\0\0\0\0\0\0\0\0",
            vm_addr: text_start,
            vm_size: utils::round_up(encoding.instructions.len(), page_size) as u64,
            file_offset: 0,
            file_size: 0, // Backpatched.
            max_vmem_protect: Permissions::Read as u32 | Permissions::Exec as u32,
            init_vmem_protect: Permissions::Read as u32 | Permissions::Exec as u32,
            sections: vec![Section {
                section_name: *b"__text\0\0\0\0\0\0\0\0\0\0",
                segment_name: *b"__TEXT\0\0\0\0\0\0\0\0\0\0",
                section_addr: text_start,
                section_size: encoding.instructions.len() as u64,
                section_file_offset: 0, // Backpatched.
                alignment: 0,
                relocations_file_offset: 0,
                relocations_count: 0,
                flags: SectionFlag::OnlyContainsTrueMachineInstructions as u32
                    | SectionFlag::ContainsSomeMachineInstructions as u32,
                typ: 0,
                reserved: [0; 3],
            }],
            flags: 0,
        }),
    ];
    let cmds_bytes_count = cmds.iter().map(|x| x.bin_size()).sum::<usize>() as u32;
    let file_size = utils::round_up(
        cmds_bytes_count as usize + encoding.instructions.len(),
        page_size,
    );
    // Machine instructions follow the header and load commands.
    cmds[1].as_segment_load_mut().unwrap().sections[0].section_file_offset =
        std::mem::size_of::<Header>() as u32 + cmds_bytes_count;
    cmds[1].as_segment_load_mut().unwrap().file_size =
        utils::round_up(cmds[1].bin_size() + encoding.instructions.len(), page_size) as u64;

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
        let mut written = 0;
        cmd.write(w)?;
        written += cmd.bin_size();

        if let Some(seg) = cmd.as_segment_load() {
            if seg.name == *b"__TEXT\0\0\0\0\0\0\0\0\0\0" {
                w.write_all(&encoding.instructions)?;
                written += encoding.instructions.len();
            }

            if seg.file_size != 0 {
                let padding = seg.file_size as usize - written;
                for _ in 0..padding {
                    w.write_all(&[0])?;
                }
            }
        }
    }

    trace!("macho: written {} bytes", file_size);

    w.flush()
}

pub fn write_to_file(file_name: &str, encoding: &Encoding) -> std::io::Result<()> {
    let mut opts = OpenOptions::new();
    opts.create(true).write(true);
    #[cfg(unix)]
    opts.mode(0o755);

    let mut file = opts.open(file_name)?;
    trace!("macho: action=write file={}", file_name);

    file.set_len(0)?;

    write(&mut file, encoding)
}
