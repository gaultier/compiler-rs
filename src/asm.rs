use std::{collections::BTreeMap, io::Write};

use log::trace;
use serde::Serialize;

use crate::{
    amd64,
    ir::{self},
    origin::Origin,
    register_alloc::{MemoryLocation, RegisterMapping},
};

#[repr(u8)]
pub enum ArchKind {
    Amd64,
    // TODO
}

pub(crate) struct Abi {
    pub(crate) gprs: Vec<Register>,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum OperandSize {
    One = 1,
    Two = 2,
    Four = 4,
    Eight = 8,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum InstructionKind {
    Amd64(amd64::InstructionKind),
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Register {
    Amd64(amd64::Register),
}

#[derive(Serialize, Debug)]
pub struct VInstruction {
    pub kind: InstructionKind,
    pub operands: Vec<ir::Operand>,
    pub origin: Origin,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum Mutability {
    Read,
    Write,
    ReadWrite,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub struct Operand {
    pub operand_size: OperandSize,
    pub kind: OperandKind,
    pub implicit: bool,
    pub mutability: Mutability,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum OperandKind {
    Register(Register),
    Immediate(u64),
    Stack(usize),
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub operands: Vec<Operand>,
    pub origin: Origin,
}

pub type EvalResult = BTreeMap<MemoryLocation, ir::Value>;

pub fn eval(instructions: &[Instruction]) -> EvalResult {
    match instructions.first().map(|ins| ins.kind) {
        Some(InstructionKind::Amd64(_)) => {
            let mut interpreter = amd64::Interpreter::new();
            interpreter.eval(instructions);
            interpreter.state
        }
        _ => EvalResult::new(),
    }
}

pub(crate) fn ir_to_vcode(irs: &[ir::Instruction], target_arch: &ArchKind) -> Vec<VInstruction> {
    match target_arch {
        ArchKind::Amd64 => amd64::ir_to_vcode(irs),
    }
}

pub(crate) fn abi(target_arch: &ArchKind) -> Abi {
    match target_arch {
        ArchKind::Amd64 => amd64::abi(),
    }
}

impl Operand {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match &self.kind {
            OperandKind::Register(register) => w.write_all(register.to_str().as_bytes()),
            OperandKind::Immediate(n) => write!(w, "{}", n),
            OperandKind::Stack(off) => write!(w, "sp + {}", off),
        }
    }
}

impl Instruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(self.kind.to_str().as_bytes())?;

        self.operands
            .iter()
            .filter(|o| !o.implicit)
            .enumerate()
            .try_for_each(|(i, o)| {
                if i == 0 {
                    write!(w, " ")?;
                } else {
                    write!(w, ", ")?;
                }
                o.write(w)
            })?;

        writeln!(w)
    }
}

impl InstructionKind {
    pub(crate) fn arch(&self) -> ArchKind {
        match self {
            InstructionKind::Amd64(_) => ArchKind::Amd64,
        }
    }

    pub(crate) fn to_str(self) -> &'static str {
        match self {
            InstructionKind::Amd64(instruction_kind) => instruction_kind.to_str(),
        }
    }

    pub(crate) fn get_in_out(&self) -> Vec<format::Operand> {
        match self {
            InstructionKind::Amd64(k) => k.get_in_out(),
        }
    }
}

impl From<&MemoryLocation> for OperandKind {
    fn from(value: &MemoryLocation) -> Self {
        match value {
            MemoryLocation::Register(reg) => OperandKind::Register(*reg),
            MemoryLocation::Stack(off) => OperandKind::Stack(*off),
        }
    }
}

impl From<&OperandKind> for MemoryLocation {
    fn from(value: &OperandKind) -> Self {
        match value {
            OperandKind::Register(register) => MemoryLocation::Register(*register),
            OperandKind::Immediate(_imm) => panic!(),
            OperandKind::Stack(off) => MemoryLocation::Stack(*off),
        }
    }
}

impl Register {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            Register::Amd64(r) => r.to_str(),
        }
    }
}

impl VInstruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(self.kind.to_str().as_bytes())?;

        for op in &self.operands {
            write!(w, " ")?;
            op.write(w)?;
        }

        writeln!(w)
    }
}

pub(crate) struct Stack {
    pub(crate) offset: usize,
}

pub(crate) struct Emitter {
    stack: Stack,
}

impl Stack {
    pub(crate) fn new_slot(&mut self, size: usize, align: usize) -> usize {
        let padding = (0usize).wrapping_sub(self.offset) & (align - 1);
        let res = self.offset + padding;

        self.offset += res + size;

        res
    }
}

pub(crate) fn emit_store(
    dst: &MemoryLocation,
    src: &OperandKind,
    arch: &ArchKind,
    size: &OperandSize,
) -> Vec<Instruction> {
    match arch {
        ArchKind::Amd64 => amd64::emit_store(dst, src, size),
    }
}

impl Emitter {
    pub(crate) fn new() -> Self {
        Self {
            stack: Stack { offset: 0 },
        }
    }

    pub(crate) fn vcode_to_asm(
        &mut self,
        vcode: &[VInstruction],
        vreg_to_memory_location: &mut RegisterMapping,
    ) -> Vec<Instruction> {
        let mut instructions = Vec::with_capacity(vcode.len());
        let mut spills = RegisterMapping::new();

        for vins in vcode {
            let in_out = vins.kind.get_in_out();
            for (i, fmt_op) in in_out.iter().enumerate() {
                if let format::Operand {
                    location: format::Location::FixedRegister(fixed_preg),
                    //mutability: Mutability::Write | Mutability::ReadWrite,
                    ..
                } = fmt_op
                {
                    let op = vins.operands[i];
                    if let ir::Operand::VirtualRegister(vreg) = op {
                        match vreg_to_memory_location.get(&vreg).unwrap() {
                            MemoryLocation::Register(preg) if preg == fixed_preg => {
                                // No need to shuffle things around, already in the right place.
                                continue;
                            }
                            src => {
                                let stack_offset = self.stack.new_slot(8, 8); // FIXME
                                let store = emit_store(
                                    &MemoryLocation::Stack(stack_offset),
                                    &(src.into()),
                                    &vins.kind.arch(),
                                    &OperandSize::Eight,
                                );
                                instructions.extend(store);
                                spills.insert(vreg, MemoryLocation::Stack(stack_offset));
                                trace!("spill: vreg={:?} sp={}", vreg, stack_offset);

                                let load = emit_store(
                                    &MemoryLocation::Register(*fixed_preg),
                                    &(src.into()),
                                    &vins.kind.arch(),
                                    &OperandSize::Eight,
                                );
                                instructions.extend(load);
                                trace!("shuffle: dst_preg={:?} src={:#?}", fixed_preg, src);
                                vreg_to_memory_location
                                    .insert(vreg, MemoryLocation::Register(*fixed_preg));
                            }
                        }
                    }
                }
            }

            let operands = vins
                .operands
                .iter()
                .map(|op| match op {
                    ir::Operand::VirtualRegister(vreg) => {
                        let loc = vreg_to_memory_location.get(vreg).unwrap();
                        Operand {
                            operand_size: OperandSize::Eight,
                            kind: loc.into(),
                            // FIXME: get rid of these fields?
                            implicit: false,
                            mutability: Mutability::Read,
                        }
                    }
                    ir::Operand::Num(num) => Operand {
                        operand_size: OperandSize::Eight,
                        kind: OperandKind::Immediate(*num),
                        implicit: false,
                        mutability: Mutability::Read,
                    },
                })
                .collect::<Vec<Operand>>();

            let ins = Instruction {
                kind: vins.kind,
                operands,
                origin: vins.origin,
            };
            instructions.push(ins);
        }

        instructions
    }
}

pub(crate) mod format {
    use crate::asm::{Mutability, Register};

    pub(crate) enum Location {
        // Fixed registers.
        FixedRegister(Register),

        Imm64,
        Rm64,
        R64,
        Memory, // Memory
    }

    pub(crate) struct Operand {
        pub(crate) location: Location,
        pub(crate) mutability: Mutability,
        pub(crate) implicit: bool,
        // TODO: extension, align
    }
}
