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
    SegmentLoad(SegmentLoadCommand),
    UnixThread(UnixThreadCommand),
}

struct UnixThreadStateX64 {
    rax: u64,
    rbx: u64,
    rcx: u64,
    rdx: u64,
    rdi: u64,
    rsi: u64,
    rbp: u64,
    rsp: u64,
    r8: u64,
    r9: u64,
    r10: u64,
    r11: u64,
    r12: u64,
    r13: u64,
    r14: u64,
    r15: u64,
    rip: u64,
    rflags: u64,
    cs: u64,
    fs: u64,
    gs: u64,
}

enum UnixThreadState {
    X64(UnixThreadStateX64),
    // TODO: ARM.
}

struct UnixThreadCommand {
    unix_thread_state: UnixThreadState,
    // In theory it's a variable amount of variables here but for our purpose there is only one.
}

struct SegmentLoadCommand {
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
    fn kind(&self) -> u32 {
        match self {
            LoadCommand::SegmentLoad(x) => x.kind(),
            LoadCommand::UnixThread(x) => x.kind(),
        }
    }

    fn size(&self) -> u32 {
        match self {
            LoadCommand::SegmentLoad(x) => x.size(),
            LoadCommand::UnixThread(x) => x.size(),
        }
    }

    fn as_segment_load(&self) -> Option<&SegmentLoadCommand> {
        match self {
            LoadCommand::SegmentLoad(x) => Some(x),
            _ => None,
        }
    }

    fn as_segment_load_mut(&mut self) -> Option<&mut SegmentLoadCommand> {
        match self {
            LoadCommand::SegmentLoad(x) => Some(x),
            _ => None,
        }
    }

    fn as_unix_thread_mut(&mut self) -> Option<&mut UnixThreadCommand> {
        match self {
            LoadCommand::UnixThread(x) => Some(x),
            _ => None,
        }
    }

    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(&self.kind().to_le_bytes())?;
        w.write_all(&self.size().to_le_bytes())?;

        dbg!(self.kind(), self.size());

        match self {
            LoadCommand::SegmentLoad(x) => x.write(w),
            LoadCommand::UnixThread(x) => x.write(w),
        }
    }
}

impl UnixThreadStateX64 {
    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(&self.rax.to_le_bytes())?;
        w.write_all(&self.rbx.to_le_bytes())?;
        w.write_all(&self.rcx.to_le_bytes())?;
        w.write_all(&self.rdx.to_le_bytes())?;
        w.write_all(&self.rdi.to_le_bytes())?;
        w.write_all(&self.rsi.to_le_bytes())?;
        w.write_all(&self.rbp.to_le_bytes())?;
        w.write_all(&self.rsp.to_le_bytes())?;
        w.write_all(&self.r8.to_le_bytes())?;
        w.write_all(&self.r9.to_le_bytes())?;
        w.write_all(&self.r10.to_le_bytes())?;
        w.write_all(&self.r11.to_le_bytes())?;
        w.write_all(&self.r12.to_le_bytes())?;
        w.write_all(&self.r13.to_le_bytes())?;
        w.write_all(&self.r14.to_le_bytes())?;
        w.write_all(&self.r15.to_le_bytes())?;
        w.write_all(&self.rip.to_le_bytes())?;
        w.write_all(&self.rflags.to_le_bytes())?;
        w.write_all(&self.cs.to_le_bytes())?;
        w.write_all(&self.fs.to_le_bytes())?;
        w.write_all(&self.gs.to_le_bytes())?;

        Ok(())
    }
}

impl UnixThreadState {
    fn flavor(&self) -> u32 {
        match self {
            UnixThreadState::X64(_) => 4,
        }
    }

    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self {
            UnixThreadState::X64(x) => x.write(w),
        }
    }

    fn size(&self) -> u32 {
        let res = match self {
            UnixThreadState::X64(_) => 168,
        };

        // Must be a multiple of size(u32).
        assert_eq!(res % 4, 0);

        res
    }
}

impl UnixThreadCommand {
    fn size(&self) -> u32 {
        let res = 8 + 4 /* flavor */ + 4 /* count */ + self.unix_thread_state.size();

        // Must be a multiple of size(u32).
        assert_eq!(res % 4, 0);
        // Must include load command kind + size.
        assert!(res >= 8);

        res
    }

    fn kind(&self) -> u32 {
        5
    }

    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        let flavor: u32 = self.unix_thread_state.flavor();
        w.write_all(&flavor.to_le_bytes())?;

        let count: u32 = 168 / std::mem::size_of::<u32>() as u32;
        w.write_all(&count.to_le_bytes())?;

        self.unix_thread_state.write(w)?;

        Ok(())
    }
}

impl SegmentLoadCommand {
    fn kind(&self) -> u32 {
        0x19
    }

    fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
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

    fn size(&self) -> u32 {
        let res = 72
            + self
                .sections
                .iter()
                .map(|x: &Section| x.size())
                .sum::<u32>();

        // Must be a multiple of size(u32).
        assert_eq!(res % 4, 0);
        // Must include load command kind + size.
        assert!(res >= 8);

        res
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

    fn size(&self) -> u32 {
        let res = 80;

        // Must be a multiple of size(u32).
        assert_eq!(res % 4, 0);

        res
    }
}

pub fn write<W: Write>(w: &mut W, encoding: &Encoding) -> std::io::Result<()> {
    assert_eq!(std::mem::size_of::<Header>(), 32);

    let page_size = 4 * 1024; // TODO: On ARM: 16KiB.
    let text_start = 1u64 << 32;
    let mut cmds = [
        LoadCommand::SegmentLoad(SegmentLoadCommand {
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
        LoadCommand::UnixThread(UnixThreadCommand {
            unix_thread_state: UnixThreadState::X64(UnixThreadStateX64 {
                rax: 0,
                rbx: 0,
                rcx: 0,
                rdx: 0,
                rdi: 0,
                rsi: 0,
                rbp: 0,
                rsp: 0,
                r8: 0,
                r9: 0,
                r10: 0,
                r11: 0,
                r12: 0,
                r13: 0,
                r14: 0,
                r15: 0,
                rip: 0, // Backpatched.
                rflags: 0,
                cs: 0,
                fs: 0,
                gs: 0,
            }),
        }),
        LoadCommand::SegmentLoad(SegmentLoadCommand {
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
    let cmd_text_idx = 2;
    assert_eq!(
        cmds[cmd_text_idx].as_segment_load().unwrap().name,
        *b"__TEXT\0\0\0\0\0\0\0\0\0\0"
    );

    let cmds_bytes_count = cmds.iter().map(|x| x.size() as usize).sum::<usize>() as u32;
    // FIXME
    let file_size = utils::round_up(
        std::mem::size_of::<Header>() + cmds_bytes_count as usize + encoding.instructions.len(),
        page_size,
    );
    // Machine instructions follow the header and load commands.
    cmds[cmd_text_idx].as_segment_load_mut().unwrap().file_size = utils::round_up(
        std::mem::size_of::<Header>() + cmds_bytes_count as usize,
        page_size,
    ) as u64;

    // Backpatch fields.
    {
        let vm_text_start =
            std::mem::size_of::<Header>() as u64 + cmds_bytes_count as u64 + text_start;
        cmds[cmd_text_idx].as_segment_load_mut().unwrap().sections[0].section_addr = vm_text_start;
        match &mut cmds[1].as_unix_thread_mut().unwrap().unix_thread_state {
            UnixThreadState::X64(unix_thread_state_x64) => {
                unix_thread_state_x64.rip = vm_text_start
            }
        };
        cmds[cmd_text_idx].as_segment_load_mut().unwrap().sections[0].section_file_offset =
            std::mem::size_of::<Header>() as u32 + cmds_bytes_count;
    }

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

    let mut written = std::mem::size_of::<Header>();
    for cmd in &mut cmds {
        cmd.write(w)?;
        written += cmd.size() as usize;
    }

    // Write the instructions.

    w.write_all(&encoding.instructions)?;
    written += encoding.instructions.len();

    let padding = utils::round_up(written, page_size) - written;
    for _ in 0..padding {
        w.write_all(&[0])?;
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
