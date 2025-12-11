use serde::Serialize;

use crate::{
    asm::{
        self, Abi, EvalResult, InstructionInOut, InstructionInOutOperand, Operand, OperandKind,
        VInstruction,
    },
    ir::{self, Value},
    register_alloc::MemoryLocation,
};

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

fn instruction_selection(ins: &ir::Instruction) -> Vec<VInstruction> {
    match (&ins.kind, &ins.lhs, &ins.rhs) {
        (
            ir::InstructionKind::IAdd,
            Some(ir::Operand::VirtualRegister(lhs)),
            Some(ir::Operand::VirtualRegister(rhs)),
        ) => vec![
            VInstruction {
                kind: asm::InstructionKind::Amd64(InstructionKind::Mov_R_RM),
                dst: Some(ir::Operand::VirtualRegister(ins.res_vreg.unwrap())),
                operands: vec![ir::Operand::VirtualRegister(*lhs)],
                origin: ins.origin,
            },
            VInstruction {
                kind: asm::InstructionKind::Amd64(InstructionKind::Add_R_RM),
                dst: Some(ir::Operand::VirtualRegister(ins.res_vreg.unwrap())),
                operands: vec![ir::Operand::VirtualRegister(*rhs)],
                origin: ins.origin,
            },
        ],
        (
            ir::InstructionKind::IMultiply,
            Some(ir::Operand::VirtualRegister(lhs)),
            Some(ir::Operand::VirtualRegister(rhs)),
        ) => vec![
            VInstruction {
                kind: asm::InstructionKind::Amd64(InstructionKind::Mov_R_RM),
                dst: Some(ir::Operand::VirtualRegister(ins.res_vreg.unwrap())),
                operands: vec![ir::Operand::VirtualRegister(*lhs)],
                origin: ins.origin,
            },
            VInstruction {
                kind: asm::InstructionKind::Amd64(InstructionKind::IMul_R_RM),
                dst: Some(ir::Operand::VirtualRegister(ins.res_vreg.unwrap())),
                operands: vec![ir::Operand::VirtualRegister(*rhs)],
                origin: ins.origin,
            },
        ],
        (
            ir::InstructionKind::IDivide,
            Some(ir::Operand::VirtualRegister(lhs)),
            Some(ir::Operand::VirtualRegister(rhs)),
        ) => vec![
            VInstruction {
                kind: asm::InstructionKind::Amd64(InstructionKind::Mov_R_RM),
                dst: Some(ir::Operand::VirtualRegister(ins.res_vreg.unwrap())),
                operands: vec![ir::Operand::VirtualRegister(*lhs)],
                origin: ins.origin,
            },
            VInstruction {
                kind: asm::InstructionKind::Amd64(InstructionKind::IDiv),
                dst: Some(ir::Operand::VirtualRegister(ins.res_vreg.unwrap())),
                operands: vec![ir::Operand::VirtualRegister(*rhs)],
                origin: ins.origin,
            },
        ],
        (ir::InstructionKind::Set, Some(ir::Operand::VirtualRegister(lhs)), None) => {
            vec![VInstruction {
                kind: asm::InstructionKind::Amd64(InstructionKind::Mov_R_RM),
                dst: Some(ir::Operand::VirtualRegister(ins.res_vreg.unwrap())),
                operands: vec![ir::Operand::VirtualRegister(*lhs)],
                origin: ins.origin,
            }]
        }
        (ir::InstructionKind::Set, Some(ir::Operand::Num(num)), None) => vec![VInstruction {
            kind: asm::InstructionKind::Amd64(InstructionKind::Mov_R_Imm),
            dst: Some(ir::Operand::VirtualRegister(ins.res_vreg.unwrap())),
            operands: vec![ir::Operand::Num(*num)],
            origin: ins.origin,
        }],
        _ => panic!("invalid IR operands"),
    }
}

pub fn ir_to_vcode(irs: &[ir::Instruction]) -> Vec<VInstruction> {
    let mut res = Vec::with_capacity(irs.len());

    for ir in irs {
        res.extend(instruction_selection(ir));
    }

    res
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
                    InstructionInOutOperand::FixedRegister((&Register::Rdx).into()),
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

impl Register {
    pub(crate) fn to_str(self) -> &'static str {
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
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            InstructionKind::Mov_R_RM | InstructionKind::Mov_R_Imm => "mov",
            InstructionKind::Add_R_RM => "add",
            InstructionKind::IMul_R_RM => "imul",
            InstructionKind::IDiv => "idiv",
        }
    }
}

pub fn eval(instructions: &[asm::Instruction]) -> EvalResult {
    let mut res = EvalResult::new();

    for ins in instructions {
        let asm::InstructionKind::Amd64(kind) = ins.kind;

        match kind {
            InstructionKind::Mov_R_RM => {
                assert_eq!(ins.operands.len(), 2);

                let dst_reg = match &ins.operands[0] {
                    Operand {
                        kind: OperandKind::Register(reg),
                        ..
                    } => reg,
                    _ => panic!("invalid dst"),
                };

                match ins.operands[1].kind {
                    asm::OperandKind::Register(reg) => {
                        let op_value = *res
                            .get(&MemoryLocation::Register(reg))
                            .unwrap_or(&Value::Num(0));

                        *res.entry(MemoryLocation::Register(*dst_reg))
                            .or_insert(Value::Num(0)) = op_value;
                    }
                    _ => panic!("invalid operand for mov_r_rm instruction"),
                };
            }
            InstructionKind::Mov_R_Imm => {
                assert_eq!(ins.operands.len(), 2);

                let dst_reg = match &ins.operands[0] {
                    Operand {
                        kind: OperandKind::Register(reg),
                        ..
                    } => reg,
                    _ => panic!("invalid dst"),
                };

                match ins.operands[1].kind {
                    asm::OperandKind::Immediate(imm) => {
                        *res.entry(MemoryLocation::Register(*dst_reg))
                            .or_insert(Value::Num(0)) = Value::Num(imm);
                    }
                    _ => panic!("invalid operand for mov_r_rm instruction"),
                };
            }
            InstructionKind::Add_R_RM => {
                assert_eq!(ins.operands.len(), 2);

                let dst_reg = match &ins.operands[0] {
                    Operand {
                        kind: OperandKind::Register(reg),
                        ..
                    } => reg,
                    _ => panic!("invalid dst"),
                };

                match ins.operands[1].kind {
                    asm::OperandKind::Register(op) => {
                        let op_value = *res
                            .get(&MemoryLocation::Register(op))
                            .unwrap_or(&Value::Num(0));

                        res.entry(MemoryLocation::Register(*dst_reg))
                            .and_modify(|e| {
                                *e = Value::Num(op_value.as_num() + e.as_num());
                            })
                            .or_insert(Value::Num(0));
                    }
                    _ => panic!("invalid operand for add_r_rm instruction"),
                };
            }
            InstructionKind::IMul_R_RM => {
                assert_eq!(ins.operands.len(), 2);

                let dst_reg = match &ins.operands[0] {
                    Operand {
                        kind: OperandKind::Register(reg),
                        ..
                    } => reg,
                    _ => panic!("invalid dst"),
                };

                match ins.operands[1].kind {
                    asm::OperandKind::Register(op) => {
                        let op_value = *res
                            .get(&MemoryLocation::Register(op))
                            .unwrap_or(&Value::Num(0));

                        res.entry(MemoryLocation::Register(*dst_reg))
                            .and_modify(|e| {
                                *e = Value::Num(op_value.as_num() * e.as_num());
                            })
                            .or_insert(Value::Num(0));
                    }
                    _ => panic!("invalid operand for imul_r_rm instruction"),
                };
            }
            InstructionKind::IDiv => {
                assert_eq!(ins.operands.len(), 2);

                let dst_reg = match &ins.operands[0] {
                    Operand {
                        kind: OperandKind::Register(reg),
                        ..
                    } => reg,
                    _ => panic!("invalid dst"),
                };
                assert_eq!(dst_reg, &asm::Register::Amd64(Register::Rax));

                match ins.operands[1].kind {
                    asm::OperandKind::Register(op) => {
                        let divisor = *res.get(&MemoryLocation::Register(op)).unwrap();
                        let quotient = res.get_mut(&MemoryLocation::Register(*dst_reg)).unwrap();

                        let rem = Value::Num(quotient.as_num() % divisor.as_num());
                        *quotient = Value::Num(quotient.as_num() / divisor.as_num());

                        res.insert(
                            MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                            rem,
                        );
                    }
                    _ => panic!("invalid operand for idiv_r_rm instruction"),
                };
            }
        }
    }

    res
}
