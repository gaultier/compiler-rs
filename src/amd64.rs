use std::{io::Write, panic};

use serde::Serialize;

use crate::{
    asm::{self, Abi, OperandSize, VInstruction},
    ir::{self},
    origin::Origin,
    register_alloc::{self, MemoryLocation, RegAlloc},
};

#[derive(Serialize, Debug, Clone, Copy)]
#[repr(u8)]
pub enum Register {
    Rax,
    Rbx,
    Rcx,
    Rdx,
    Rdi,
    Rsi,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl From<&register_alloc::Register> for Register {
    fn from(value: &register_alloc::Register) -> Self {
        match value.as_u8() {
            value if value == Register::Rax as u8 => Register::Rax,
            value if value == Register::Rbx as u8 => Register::Rbx,
            value if value == Register::Rcx as u8 => Register::Rcx,
            value if value == Register::Rdx as u8 => Register::Rdx,
            value if value == Register::Rdi as u8 => Register::Rdi,
            value if value == Register::Rsi as u8 => Register::Rsi,
            value if value == Register::R8 as u8 => Register::R8,
            value if value == Register::R9 as u8 => Register::R9,
            value if value == Register::R10 as u8 => Register::R10,
            value if value == Register::R11 as u8 => Register::R11,
            value if value == Register::R12 as u8 => Register::R12,
            value if value == Register::R13 as u8 => Register::R13,
            value if value == Register::R14 as u8 => Register::R14,
            value if value == Register::R15 as u8 => Register::R15,
            _ => panic!("value out of range"),
        }
    }
}
impl From<&Register> for register_alloc::Register {
    fn from(value: &Register) -> Self {
        register_alloc::Register(*value as u8)
    }
}

pub(crate) const GPRS: [Register; 14] = [
    Register::Rax,
    Register::Rbx,
    Register::Rcx,
    Register::Rdx,
    Register::Rdi,
    Register::Rsi,
    Register::R8,
    Register::R9,
    Register::R10,
    Register::R11,
    Register::R12,
    Register::R13,
    Register::R14,
    Register::R15,
];

pub fn abi() -> Abi {
    Abi {
        arch_kind: asm::ArchKind::Amd64,
        gprs: GPRS.iter().map(|r| r.into()).collect(),
    }
}

#[derive(Serialize, Debug)]
#[allow(non_camel_case_types)]
pub enum InstructionKind {
    Mov_R_RM,
    Mov_R_Imm,
    Add_R_RM,
    IMul_R_RM,
    IDiv,
}

#[derive(Serialize, Debug)]
pub enum InstructionInOutOperand {
    FixedRegister(Register),
    RegisterPosition(u8),
}

#[derive(Serialize, Debug)]
pub struct InstructionInOut {
    registers_read: Vec<InstructionInOutOperand>,
    registers_written: Vec<InstructionInOutOperand>,
    // TODO: Maybe also record flags read/written?
}

#[derive(Serialize, Debug, Clone, Copy)]
pub enum OperandKind {
    Register(Register),
    Immediate(u64),
}

#[derive(Serialize, Debug, Clone, Copy)]
pub struct Operand {
    operand_size: OperandSize,
    kind: OperandKind,
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    kind: InstructionKind,
    lhs: Option<Operand>,
    rhs: Option<Operand>,
    origin: Origin,
}

// TODO: For now it is 1:1 but in the future it could be 1:N or N:1.
fn instruction_selection(ins: &ir::Instruction) -> InstructionKind {
    match (&ins.kind, &ins.lhs, &ins.rhs) {
        (
            ir::InstructionKind::Add,
            Some(ir::Operand::VirtualRegister(_)),
            Some(ir::Operand::VirtualRegister(_)),
        ) => InstructionKind::Add_R_RM,
        (
            ir::InstructionKind::Multiply,
            Some(ir::Operand::VirtualRegister(_)),
            Some(ir::Operand::VirtualRegister(_)),
        ) => InstructionKind::IMul_R_RM,
        (
            ir::InstructionKind::Set,
            Some(ir::Operand::VirtualRegister(_)),
            Some(ir::Operand::VirtualRegister(_)),
        ) => InstructionKind::Mov_R_RM,
        (
            ir::InstructionKind::Set,
            Some(ir::Operand::VirtualRegister(_)),
            Some(ir::Operand::Num(_)),
        ) => InstructionKind::Mov_R_Imm,
        _ => panic!("invalid IR operands"),
    }
}

pub fn ir_to_vcode(irs: &[ir::Instruction]) -> Vec<VInstruction> {
    let mut res = Vec::with_capacity(irs.len());

    for ir in irs {
        let ins = VInstruction {
            kind: asm::InstructionKind::Amd64(instruction_selection(ir)),
            lhs: ir.lhs,
            rhs: ir.rhs,
            origin: ir.origin,
        };
        res.push(ins);
    }

    res
}

pub struct Emitter {
    pub instructions: Vec<Instruction>,
}

impl InstructionKind {
    pub fn get_in_out(&self) -> InstructionInOut {
        match self {
            InstructionKind::Mov_R_RM => InstructionInOut {
                registers_read: vec![InstructionInOutOperand::RegisterPosition(1)],
                registers_written: vec![InstructionInOutOperand::RegisterPosition(0)],
            },
            InstructionKind::Mov_R_Imm => InstructionInOut {
                registers_read: vec![],
                registers_written: vec![InstructionInOutOperand::RegisterPosition(0)],
            },
            InstructionKind::Add_R_RM => InstructionInOut {
                registers_read: vec![
                    InstructionInOutOperand::RegisterPosition(0),
                    InstructionInOutOperand::RegisterPosition(1),
                ],
                registers_written: vec![InstructionInOutOperand::RegisterPosition(0)],
            },
            InstructionKind::IMul_R_RM => InstructionInOut {
                registers_read: vec![
                    InstructionInOutOperand::RegisterPosition(0),
                    InstructionInOutOperand::RegisterPosition(1),
                ],
                registers_written: vec![InstructionInOutOperand::RegisterPosition(0)],
            },
            InstructionKind::IDiv => InstructionInOut {
                registers_read: vec![
                    InstructionInOutOperand::FixedRegister(Register::Rax),
                    InstructionInOutOperand::RegisterPosition(1),
                ],
                registers_written: vec![
                    InstructionInOutOperand::FixedRegister(Register::Rax),
                    InstructionInOutOperand::FixedRegister(Register::Rdx),
                ],
            },
        }
    }
}

impl OperandKind {
    pub fn is_immediate(&self) -> bool {
        match self {
            OperandKind::Immediate(_) => true,
            _ => false,
        }
    }
}

fn ir_operand_to_asm(op: &Option<ir::Operand>, regalloc: &RegAlloc) -> Option<Operand> {
    match op {
        Some(ir::Operand::VirtualRegister(vreg)) => {
            let memory_location = regalloc.get(vreg).unwrap();
            let kind = match memory_location {
                MemoryLocation::Register(register) => OperandKind::Register(register.into()),
                MemoryLocation::Stack(_) => todo!(),
            };
            Some(Operand {
                operand_size: OperandSize::Eight, // TODO
                kind,
            })
        }
        Some(ir::Operand::Num(num)) => Some(Operand {
            operand_size: OperandSize::Eight,
            kind: OperandKind::Immediate(*num),
        }),
        None => None,
    }
}

fn memory_location_to_asm_operand(location: &MemoryLocation) -> Operand {
    match location {
        MemoryLocation::Register(register) => Operand {
            operand_size: OperandSize::Eight,
            kind: OperandKind::Register(register.into()),
        },
        MemoryLocation::Stack(_) => todo!(),
    }
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
        }
    }

    pub fn emit(&mut self, irs: &[ir::Instruction], regalloc: &RegAlloc) {
        self.instructions.reserve(irs.len());

        for ir in irs {
            match ir.kind {
                ir::InstructionKind::Multiply => {
                    let res_location = regalloc.get(&ir.res_vreg.unwrap()).unwrap();
                    let res_operand = memory_location_to_asm_operand(res_location);
                    let rhs_mov = ir_operand_to_asm(&ir.lhs, regalloc);

                    let ins_mov = Instruction {
                        kind: InstructionKind::Mov_R_RM,
                        lhs: Some(res_operand.clone()),
                        rhs: rhs_mov,
                        origin: ir.origin,
                    };
                    self.instructions.push(ins_mov);

                    let rhs_add = ir_operand_to_asm(&ir.rhs, regalloc);

                    let ins_add = Instruction {
                        kind: InstructionKind::IMul_R_RM,
                        lhs: Some(res_operand),
                        rhs: rhs_add,
                        origin: ir.origin,
                    };
                    self.instructions.push(ins_add);
                }
                ir::InstructionKind::Add => {
                    let res_location = regalloc.get(&ir.res_vreg.unwrap()).unwrap();
                    let res_operand = memory_location_to_asm_operand(res_location);
                    let rhs_mov = ir_operand_to_asm(&ir.lhs, regalloc);

                    let ins_mov = Instruction {
                        kind: InstructionKind::Mov_R_RM,
                        lhs: Some(res_operand.clone()),
                        rhs: rhs_mov,
                        origin: ir.origin,
                    };
                    self.instructions.push(ins_mov);

                    let rhs_add = ir_operand_to_asm(&ir.rhs, regalloc);

                    let ins_add = Instruction {
                        kind: InstructionKind::Add_R_RM,
                        lhs: Some(res_operand),
                        rhs: rhs_add,
                        origin: ir.origin,
                    };
                    self.instructions.push(ins_add);
                }
                ir::InstructionKind::Set => {
                    let res_location = regalloc.get(&ir.res_vreg.unwrap()).unwrap();
                    let res_operand = memory_location_to_asm_operand(res_location);
                    let rhs = ir_operand_to_asm(&ir.lhs, regalloc);
                    let ins = Instruction {
                        kind: InstructionKind::Mov_R_RM,
                        lhs: Some(res_operand),
                        rhs,
                        origin: ir.origin,
                    };
                    self.instructions.push(ins);
                }
            }
        }
    }
}

impl Register {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self {
            Register::Rax => write!(w, "rax"),
            Register::Rbx => write!(w, "rbx"),
            Register::Rcx => write!(w, "rcx"),
            Register::Rdx => write!(w, "rdx"),
            Register::Rdi => write!(w, "rdi"),
            Register::Rsi => write!(w, "rsi"),
            Register::R8 => write!(w, "r8"),
            Register::R9 => write!(w, "r9"),
            Register::R10 => write!(w, "r10"),
            Register::R11 => write!(w, "r11"),
            Register::R12 => write!(w, "r12"),
            Register::R13 => write!(w, "r13"),
            Register::R14 => write!(w, "r14"),
            Register::R15 => write!(w, "r15"),
        }
    }
}

impl Operand {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match &self.kind {
            OperandKind::Register(register) => register.write(w),
            OperandKind::Immediate(n) => write!(w, "{}", n),
        }
    }
}

impl Instruction {
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self.kind {
            InstructionKind::Mov_R_RM | InstructionKind::Mov_R_Imm => {
                write!(w, "mov ")?;
            }
            InstructionKind::Add_R_RM => {
                write!(w, "add ")?;
            }
            InstructionKind::IMul_R_RM => {
                write!(w, "imul ")?;
            }
            InstructionKind::IDiv => {
                write!(w, "idiv ")?;
            }
        };

        if let Some(lhs) = &self.lhs {
            lhs.write(w)?;
        }
        write!(w, ", ")?;

        if let Some(rhs) = &self.rhs {
            rhs.write(w)?;
        }

        writeln!(w)
    }
}
