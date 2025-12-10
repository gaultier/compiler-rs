use std::panic;

use serde::Serialize;

use crate::{
    asm::{
        self, Abi, InstructionInOut, InstructionInOutOperand, Operand, OperandKind, VInstruction,
    },
    ir::{self},
    register_alloc::{MemoryLocation, RegAlloc},
};

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

impl From<&asm::Register> for Register {
    fn from(value: &asm::Register) -> Self {
        match value {
            asm::Register::Amd64(r) => *r,
        }
    }
}

impl From<asm::Register> for Register {
    fn from(value: asm::Register) -> Self {
        (&value).into()
    }
}

impl From<&Register> for asm::Register {
    fn from(value: &Register) -> Self {
        asm::Register::Amd64(*value)
    }
}

impl From<Register> for asm::Register {
    fn from(value: Register) -> Self {
        asm::Register::Amd64(value)
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

pub(crate) fn abi() -> Abi {
    Abi {
        gprs: GPRS.iter().map(|r| r.into()).collect(),
    }
}

#[derive(Serialize, Debug, Clone, Copy)]
#[allow(non_camel_case_types)]
#[repr(u16)]
pub enum InstructionKind {
    Mov_R_RM,
    Mov_R_Imm,
    Add_R_RM,
    IMul_R_RM,
    IDiv,
}

// FIXME: Should be: `-> Vec<VInstruction>`
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
        (ir::InstructionKind::Set, Some(ir::Operand::Num(_)), None) => InstructionKind::Mov_R_Imm,
        (ir::InstructionKind::Set, Some(ir::Operand::VirtualRegister(_)), None) => {
            InstructionKind::Mov_R_RM
        }
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
            res_vreg: ir.res_vreg,
        };
        res.push(ins);
    }

    res
}

pub struct Emitter {
    pub instructions: Vec<asm::Instruction>,
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
                    InstructionInOutOperand::FixedRegister((&Register::Rax).into()),
                    InstructionInOutOperand::RegisterPosition(1),
                ],
                registers_written: vec![
                    InstructionInOutOperand::FixedRegister((&Register::Rax).into()),
                    InstructionInOutOperand::FixedRegister((&Register::Rdx).into()),
                ],
            },
        }
    }
}

fn ir_operand_to_asm(op: &Option<ir::Operand>, regalloc: &RegAlloc) -> Option<Operand> {
    match op {
        Some(ir::Operand::VirtualRegister(vreg)) => {
            let memory_location = regalloc.get(vreg).unwrap();
            let kind = match memory_location {
                MemoryLocation::Register(register) => OperandKind::Register(*register),
                MemoryLocation::Stack(_) => todo!(),
            };
            Some(Operand {
                operand_size: asm::OperandSize::Eight, // TODO
                kind,
            })
        }
        Some(ir::Operand::Num(num)) => Some(Operand {
            operand_size: asm::OperandSize::Eight,
            kind: asm::OperandKind::Immediate(*num),
        }),
        None => None,
    }
}

fn memory_location_to_asm_operand(location: &MemoryLocation) -> asm::Operand {
    match location {
        MemoryLocation::Register(register) => asm::Operand {
            operand_size: asm::OperandSize::Eight,
            kind: asm::OperandKind::Register(*register),
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

    pub fn emit(&mut self, vcode: &[VInstruction], _regalloc: &RegAlloc) {
        self.instructions.reserve(vcode.len());

        //for v in vcode {
        //    match ir.kind {
        //        ir::InstructionKind::Multiply => {
        //            let res_location = regalloc.get(&ir.res_vreg.unwrap()).unwrap();
        //            let res_operand = memory_location_to_asm_operand(res_location);
        //            let rhs_mov = ir_operand_to_asm(&ir.lhs, regalloc);
        //
        //            let ins_mov = Instruction {
        //                kind: asm::InstructionKind::Amd64(InstructionKind::Mov_R_RM),
        //                lhs: Some(res_operand.clone()),
        //                rhs: rhs_mov,
        //                origin: ir.origin,
        //            };
        //            self.instructions.push(ins_mov);
        //
        //            let rhs_add = ir_operand_to_asm(&ir.rhs, regalloc);
        //
        //            let ins_add = Instruction {
        //                kind: asm::InstructionKind::Amd64(InstructionKind::IMul_R_RM),
        //                lhs: Some(res_operand),
        //                rhs: rhs_add,
        //                origin: ir.origin,
        //            };
        //            self.instructions.push(ins_add);
        //        }
        //        ir::InstructionKind::Add => {
        //            let res_location = regalloc.get(&ir.res_vreg.unwrap()).unwrap();
        //            let res_operand = memory_location_to_asm_operand(res_location);
        //            let rhs_mov = ir_operand_to_asm(&ir.lhs, regalloc);
        //
        //            let ins_mov = Instruction {
        //                kind: asm::InstructionKind::Amd64(InstructionKind::Mov_R_RM),
        //                lhs: Some(res_operand.clone()),
        //                rhs: rhs_mov,
        //                origin: ir.origin,
        //            };
        //            self.instructions.push(ins_mov);
        //
        //            let rhs_add = ir_operand_to_asm(&ir.rhs, regalloc);
        //
        //            let ins_add = Instruction {
        //                kind: asm::InstructionKind::Amd64(InstructionKind::Add_R_RM),
        //                lhs: Some(res_operand),
        //                rhs: rhs_add,
        //                origin: ir.origin,
        //            };
        //            self.instructions.push(ins_add);
        //        }
        //        ir::InstructionKind::Set => {
        //            let res_location = regalloc.get(&ir.res_vreg.unwrap()).unwrap();
        //            let res_operand = memory_location_to_asm_operand(res_location);
        //            let rhs = ir_operand_to_asm(&ir.lhs, regalloc);
        //            let ins = Instruction {
        //                kind: asm::InstructionKind::Amd64(InstructionKind::Mov_R_RM),
        //                lhs: Some(res_operand),
        //                rhs,
        //                origin: ir.origin,
        //            };
        //            self.instructions.push(ins);
        //        }
        //    }
        //}
    }
}

impl Register {
    pub(crate) fn to_str(&self) -> &'static str {
        match self {
            Register::Rax => "rax",
            Register::Rbx => "rbx",
            Register::Rcx => "rcx",
            Register::Rdx => "rdx",
            Register::Rdi => "rdi",
            Register::Rsi => "rsi",
            Register::R8 => "r8",
            Register::R9 => "r9",
            Register::R10 => "r10",
            Register::R11 => "r11",
            Register::R12 => "r12",
            Register::R13 => "r13",
            Register::R14 => "r14",
            Register::R15 => "r15",
        }
    }
}

impl InstructionKind {
    pub(crate) fn to_str(&self) -> &'static str {
        match self {
            InstructionKind::Mov_R_RM | InstructionKind::Mov_R_Imm => "mov",
            InstructionKind::Add_R_RM => "add",
            InstructionKind::IMul_R_RM => "imul",
            InstructionKind::IDiv => "idiv",
        }
    }
}
