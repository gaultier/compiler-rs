use std::{collections::HashMap, io::Write};

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

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Register {
    Amd64(amd64::Register),
}

#[derive(Serialize, Debug)]
pub struct VInstruction {
    pub kind: InstructionKind,
    pub dst: Option<ir::Operand>,
    pub operands: Vec<ir::Operand>,
    pub origin: Origin,
}

#[derive(Serialize, Debug)]
pub enum InstructionInOutOperand {
    FixedRegister(Register),
    RegisterPosition(u8),
}

#[derive(Serialize, Debug)]
pub struct InstructionInOut {
    pub(crate) registers_read: Vec<InstructionInOutOperand>,
    pub(crate) registers_written: Vec<InstructionInOutOperand>,
    // TODO: Maybe also record flags read/written?
}

#[derive(Serialize, Debug, Clone, Copy)]
pub struct Operand {
    pub(crate) operand_size: OperandSize,
    pub(crate) kind: OperandKind,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum OperandKind {
    Register(Register),
    Immediate(u64),
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub dst: Option<Operand>,
    pub operands: Vec<Operand>,
    pub origin: Origin,
}

pub type EvalResult = HashMap<MemoryLocation, ir::Value>;

pub fn eval(instructions: &[Instruction]) -> EvalResult {
    match instructions.get(0).map(|ins| ins.kind) {
        Some(InstructionKind::Amd64(_)) => amd64::eval(instructions),
        _ => EvalResult::new(),
    }
}

impl InstructionKind {
    pub(crate) fn get_in_out(&self) -> InstructionInOut {
        match self {
            InstructionKind::Amd64(instruction_kind) => instruction_kind.get_in_out(),
        }
    }
}

impl InstructionInOut {
    pub(crate) fn get_fixed_output_reg(&self) -> Option<Register> {
        for reg in &self.registers_written {
            match reg {
                InstructionInOutOperand::FixedRegister(reg) => return Some(*reg),
                InstructionInOutOperand::RegisterPosition(_pos) => {

                    // return Some(registers_written[*pos as usize]);
                }
            }
        }
        None
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
        }
    }
}

impl Instruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(self.kind.to_str().as_bytes())?;

        if let Some(dst) = &self.dst {
            write!(w, " ")?;
            dst.write(w)?;
        }

        for op in &self.operands {
            write!(w, ", ")?;
            op.write(w)?;
        }

        writeln!(w)
    }
}

impl InstructionKind {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            InstructionKind::Amd64(instruction_kind) => instruction_kind.to_str(),
        }
    }
}

impl OperandKind {
    pub fn is_immediate(&self) -> bool {
        matches!(self, OperandKind::Immediate(_))
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

        if let Some(dst) = &self.dst {
            write!(w, " ")?;
            dst.write(w)?;
        }

        for op in &self.operands {
            write!(w, ", ")?;
            op.write(w)?;
        }

        writeln!(w)
    }
}

pub(crate) fn vcode_to_asm(
    vcode: &[VInstruction],
    vreg_to_memory_location: &RegisterMapping,
) -> Vec<Instruction> {
    let mut instructions = Vec::with_capacity(vcode.len());

    for vins in vcode {
        let dst = match vins.dst {
            Some(ir::Operand::VirtualRegister(vreg)) => match vreg_to_memory_location.get(&vreg) {
                Some(MemoryLocation::Register(preg)) => Some(Operand {
                    operand_size: OperandSize::Eight,
                    kind: OperandKind::Register(*preg),
                }),
                Some(MemoryLocation::Stack(_)) => todo!(),
                None => panic!("vreg does not have a preg"),
            },
            Some(ir::Operand::Num(_)) => panic!("invalid number as instruction destination"),
            None => None,
        };

        let operands = vins
            .operands
            .iter()
            .map(|op| match op {
                ir::Operand::VirtualRegister(vreg) => match vreg_to_memory_location.get(&vreg) {
                    Some(MemoryLocation::Register(preg)) => Operand {
                        operand_size: OperandSize::Eight,
                        kind: OperandKind::Register(*preg),
                    },
                    Some(MemoryLocation::Stack(_)) => todo!(),
                    None => panic!("vreg does not have a preg"),
                },
                ir::Operand::Num(num) => Operand {
                    operand_size: OperandSize::Eight,
                    kind: OperandKind::Immediate(*num),
                },
            })
            .collect::<Vec<Operand>>();

        let ins = Instruction {
            kind: vins.kind,
            dst,
            operands,
            origin: vins.origin,
        };
        instructions.push(ins);
    }

    instructions
}
