use serde::Serialize;

use crate::{
    asm::{self, Abi, EvalResult, Operand, OperandKind, OperandSize, Stack},
    ir::{self, Value},
    origin::Origin,
    register_alloc::{MemoryLocation, RegisterMapping},
};

#[derive(Serialize, Debug)]
pub(crate) struct Instruction {
    pub(crate) kind: InstructionKind,
    pub(crate) operands: Vec<Operand>,
    pub(crate) origin: Origin,
}

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
    Mov_RM_R,
    Add_R_RM,
    IMul_R_RM,
    IDiv,
    Lea,
}

// TODO: Use a free register if possible.
fn find_free_spill_slot(stack: &mut Stack, op_size: &OperandSize) -> MemoryLocation {
    let (size, align) = (op_size.as_usize(), 8); // TODO: Improve.
    let offset = stack.new_slot(size, align);
    MemoryLocation::Stack(offset)
}

fn instruction_selection(
    ins: &ir::Instruction,
    vreg_to_memory_location: &RegisterMapping,
    stack: &mut Stack,
) -> Vec<Instruction> {
    match (&ins.kind, &ins.lhs, &ins.rhs) {
        (
            ir::InstructionKind::IAdd,
            Some(ir::Operand::VirtualRegister(lhs)),
            Some(ir::Operand::VirtualRegister(rhs)),
        ) => vec![
            Instruction {
                kind: InstructionKind::Mov_R_RM,
                operands: vec![
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    ),
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(lhs).unwrap(),
                    ),
                ],
                origin: ins.origin,
            },
            Instruction {
                kind: InstructionKind::Add_R_RM,
                operands: vec![
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    ),
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(rhs).unwrap(),
                    ),
                ],
                origin: ins.origin,
            },
        ],
        (
            ir::InstructionKind::IMultiply,
            Some(ir::Operand::VirtualRegister(lhs)),
            Some(ir::Operand::VirtualRegister(rhs)),
        ) => vec![
            Instruction {
                kind: InstructionKind::Mov_R_RM,
                operands: vec![
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    ),
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(lhs).unwrap(),
                    ),
                ],
                origin: ins.origin,
            },
            Instruction {
                kind: InstructionKind::IMul_R_RM,
                operands: vec![
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    ),
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(rhs).unwrap(),
                    ),
                ],
                origin: ins.origin,
            },
        ],
        (
            ir::InstructionKind::IDivide,
            Some(ir::Operand::VirtualRegister(lhs)),
            Some(ir::Operand::VirtualRegister(rhs)),
        ) => {
            // `dst = lhs / rhs`
            // =>
            // `mov rax, lhs`
            // with: dst in rax.
            // then:
            // `idiv rhs`
            // with: dst in rax.
            let mut res = Vec::with_capacity(2);

            let lhs = vreg_to_memory_location.get(lhs).unwrap();
            // If `lhs` is already in `rax`, nothing to do.
            // Otherwise: need to spill what's in `rax` and move `lhs` to it.
            let lhs_spill_slot =
                if lhs != &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)) {
                    let spill_slot = find_free_spill_slot(stack, &OperandSize::Eight);
                    res.extend(emit_store(
                        &spill_slot,
                        &(&MemoryLocation::Register(asm::Register::Amd64(Register::Rax))).into(),
                        &OperandSize::Eight,
                    ));
                    res.extend(emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)),
                        &lhs.into(),
                        &OperandSize::Eight,
                    ));

                    Some(spill_slot)
                } else {
                    None
                };

            res.push(Instruction {
                kind: InstructionKind::IDiv,
                operands: vec![Operand::from_memory_location(
                    &OperandSize::Eight,
                    vreg_to_memory_location.get(rhs).unwrap(),
                )],
                origin: ins.origin,
            });

            let dst = vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap();
            // The quotient is now in `rax`.
            // If `dst` should be in `rax`, then nothing to do.
            // Otherwise: need to `mov dst, rax`.
            if dst != &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)) {
                emit_store(
                    dst,
                    &(&MemoryLocation::Register(asm::Register::Amd64(Register::Rax))).into(),
                    &OperandSize::Eight,
                );
            }

            // Finally: if we did a spill in the beginning, then we need to restore `lhs`
            // to its original place, i.e. : `mov lhs, spill_slot`.
            if let Some(slot) = &lhs_spill_slot {
                emit_store(lhs, &slot.into(), &OperandSize::Eight);
            }

            res
        }
        (ir::InstructionKind::Set, Some(ir::Operand::VirtualRegister(lhs)), None) => {
            vec![Instruction {
                kind: InstructionKind::Mov_R_RM,
                operands: vec![
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    ),
                    Operand::from_memory_location(
                        &OperandSize::Eight,
                        vreg_to_memory_location.get(lhs).unwrap(),
                    ),
                ],
                origin: ins.origin,
            }]
        }
        (ir::InstructionKind::Set, Some(ir::Operand::Num(num)), None) => vec![Instruction {
            kind: InstructionKind::Mov_R_Imm,
            operands: vec![
                Operand::from_memory_location(
                    &OperandSize::Eight,
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                ),
                Operand::new(&OperandSize::Eight, &OperandKind::Immediate(*num)),
            ],
            origin: ins.origin,
        }],
        _ => panic!("invalid IR operands"),
    }
}

pub(crate) fn emit(
    irs: &[ir::Instruction],
    vreg_to_memory_location: &RegisterMapping,
) -> (Vec<asm::Instruction>, Stack) {
    let mut asm = Vec::with_capacity(irs.len() * 2);
    let mut stack = Stack::new();

    for ir in irs {
        asm.extend(instruction_selection(
            ir,
            vreg_to_memory_location,
            &mut stack,
        ));
    }

    (
        asm.into_iter()
            .map(|x| asm::Instruction {
                kind: asm::InstructionKind::Amd64(x.kind),
                operands: x.operands,
                origin: x.origin,
            })
            .collect(),
        stack,
    )
}

pub(crate) fn emit_store(
    dst: &MemoryLocation,
    src: &OperandKind,
    size: &OperandSize,
) -> Vec<Instruction> {
    match (dst, src) {
        (MemoryLocation::Register(dst_reg), OperandKind::Register(src_reg)) => {
            vec![Instruction {
                kind: InstructionKind::Mov_R_RM,
                operands: vec![
                    Operand {
                        operand_size: *size,
                        kind: OperandKind::Register(*dst_reg),
                    },
                    Operand {
                        operand_size: *size,
                        kind: OperandKind::Register(*src_reg),
                    },
                ],
                origin: Origin::default(),
            }]
        }
        (MemoryLocation::Register(dst_reg), OperandKind::Immediate(src_imm)) => vec![Instruction {
            kind: InstructionKind::Mov_R_Imm,
            operands: vec![
                Operand {
                    operand_size: *size,
                    kind: OperandKind::Register(*dst_reg),
                },
                Operand {
                    operand_size: *size,
                    kind: OperandKind::Immediate(*src_imm),
                },
            ],
            origin: Origin::default(),
        }],
        (MemoryLocation::Stack(dst_stack), OperandKind::Register(src_reg)) => vec![Instruction {
            kind: InstructionKind::Mov_RM_R,
            operands: vec![
                Operand {
                    operand_size: *size,
                    kind: OperandKind::Stack(*dst_stack),
                },
                Operand {
                    operand_size: *size,
                    kind: OperandKind::Register(*src_reg),
                },
            ],
            origin: Origin::default(),
        }],
        (MemoryLocation::Stack(_), OperandKind::Immediate(_)) => todo!(),
        (MemoryLocation::Register(dst_reg), OperandKind::Stack(_)) => {
            vec![Instruction {
                kind: InstructionKind::Mov_R_RM,
                operands: vec![
                    Operand {
                        operand_size: *size,
                        kind: OperandKind::Register(*dst_reg),
                    },
                    Operand {
                        operand_size: *size,
                        kind: *src,
                    },
                ],
                origin: Origin::default(),
            }]
        }
        (MemoryLocation::Stack(_), OperandKind::Stack(_)) => todo!(),
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
            InstructionKind::Mov_RM_R | InstructionKind::Mov_R_RM | InstructionKind::Mov_R_Imm => {
                "mov"
            }
            InstructionKind::Add_R_RM => "add",
            InstructionKind::IMul_R_RM => "imul",
            InstructionKind::IDiv => "idiv",
            InstructionKind::Lea => "lea",
        }
    }
}

pub struct Interpreter {
    pub state: EvalResult,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            state: EvalResult::new(),
        }
    }

    fn store(&mut self, dst: &Operand, src: &Operand) {
        match (dst.kind, src.kind) {
            (OperandKind::Register(_), OperandKind::Register(_))
            | (OperandKind::Stack(_), OperandKind::Register(_))
            | (OperandKind::Register(_), OperandKind::Stack(_)) => {
                let value = *self.state.get(&(&src.kind).into()).unwrap();
                self.state.insert((&dst.kind).into(), value);
            }
            (OperandKind::Register(_), OperandKind::Immediate(imm))
            | (OperandKind::Stack(_), OperandKind::Immediate(imm)) => {
                self.state.insert((&dst.kind).into(), Value::Num(imm));
            }
            (OperandKind::Immediate(_), _) => panic!("invalid store destination"),
            (OperandKind::Stack(_), OperandKind::Stack(_)) => panic!("unsupported store"),
        };
    }

    fn load(&mut self, dst: &Operand, src: &Operand) {
        match (dst.kind, src.kind) {
            (OperandKind::Register(_), OperandKind::Stack(_)) => {
                let value = *self.state.get(&(&src.kind).into()).unwrap();
                self.state.insert((&dst.kind).into(), value);
            }
            _ => panic!("unsupported load"),
        };
    }

    pub fn eval(&mut self, instructions: &[asm::Instruction]) {
        for ins in instructions {
            let asm::InstructionKind::Amd64(kind) = ins.kind;

            match kind {
                InstructionKind::Mov_R_Imm
                | InstructionKind::Mov_R_RM
                | InstructionKind::Mov_RM_R => {
                    assert_eq!(ins.operands.len(), 2);
                    self.store(&ins.operands[0], &ins.operands[1]);
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
                            let op_value = *self
                                .state
                                .get(&MemoryLocation::Register(op))
                                .unwrap_or(&Value::Num(0));

                            self.state
                                .entry(MemoryLocation::Register(*dst_reg))
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
                            let op_value = *self
                                .state
                                .get(&MemoryLocation::Register(op))
                                .unwrap_or(&Value::Num(0));

                            self.state
                                .entry(MemoryLocation::Register(*dst_reg))
                                .and_modify(|e| {
                                    *e = Value::Num(op_value.as_num() * e.as_num());
                                })
                                .or_insert(Value::Num(0));
                        }
                        _ => panic!("invalid operand for imul_r_rm instruction"),
                    };
                }
                InstructionKind::IDiv => {
                    assert_eq!(ins.operands.len(), 1);

                    let dst_reg = asm::Register::Amd64(Register::Rax);

                    match ins.operands[0].kind {
                        asm::OperandKind::Register(op) => {
                            let divisor = *self.state.get(&MemoryLocation::Register(op)).unwrap();
                            let quotient = self
                                .state
                                .get_mut(&MemoryLocation::Register(dst_reg))
                                .unwrap();

                            let rem = Value::Num(quotient.as_num() % divisor.as_num());
                            *quotient = Value::Num(quotient.as_num() / divisor.as_num());

                            self.state.insert(
                                MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                                rem,
                            );
                        }
                        _ => panic!("invalid operand for idiv_r_rm instruction"),
                    };
                }
                InstructionKind::Lea => {
                    assert_eq!(ins.operands.len(), 2);
                    self.load(&ins.operands[0], &ins.operands[1]);
                }
            }
        }
    }
}
