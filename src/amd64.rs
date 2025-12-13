use log::trace;
use serde::Serialize;

use crate::{
    asm::{self, Abi, EvalResult, Operand, OperandKind, OperandSize, Stack},
    ir::{self, EvalValue},
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

pub struct Emitter {
    pub(crate) stack: Stack,
    pub(crate) asm: Vec<Instruction>,
}

impl Default for Emitter {
    fn default() -> Self {
        Self::new()
    }
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            stack: Stack::new(),
            asm: Vec::new(),
        }
    }

    // TODO: Use a free register if possible.
    fn find_free_spill_slot(&mut self, op_size: &OperandSize) -> MemoryLocation {
        let (size, align) = (op_size.as_bytes(), 8); // TODO: Improve.
        let offset = self.stack.new_slot(size, align);
        MemoryLocation::Stack(offset)
    }

    #[warn(unused_results)]
    fn instruction_selection(
        &mut self,
        ins: &ir::Instruction,
        vreg_to_memory_location: &RegisterMapping,
    ) {
        match (
            &ins.kind,
            &ins.operands.iter().nth(0),
            &ins.operands.iter().nth(1),
        ) {
            (
                ir::InstructionKind::IAdd,
                Some(ir::Operand::VirtualRegister(lhs)),
                Some(ir::Operand::VirtualRegister(rhs)),
            ) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_R_RM,
                    operands: vec![
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(lhs).unwrap(),
                        ),
                    ],
                    origin: ins.origin,
                });
                self.asm.push(Instruction {
                    kind: InstructionKind::Add_R_RM,
                    operands: vec![
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(rhs).unwrap(),
                        ),
                    ],
                    origin: ins.origin,
                });
            }
            (
                ir::InstructionKind::IMultiply,
                Some(ir::Operand::VirtualRegister(lhs)),
                Some(ir::Operand::VirtualRegister(rhs)),
            ) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_R_RM,
                    operands: vec![
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(lhs).unwrap(),
                        ),
                    ],
                    origin: ins.origin,
                });
                self.asm.push(Instruction {
                    kind: InstructionKind::IMul_R_RM,
                    operands: vec![
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(rhs).unwrap(),
                        ),
                    ],
                    origin: ins.origin,
                });
            }
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

                // `rdx` gets overwritten by `idiv`. So before issuing `idiv`, spill `rdx`.
                // At the end, we restore it.
                // TODO: Could be done conditionally by checking if `rdx` contains a meaningful value.
                // TODO: There is a case where `rdx_spill_slot` and `lhs_spill_slot` could be merged
                // into one.
                let rdx_spill_slot = {
                    let spill_slot = self.find_free_spill_slot(&OperandSize::_64);
                    self.emit_store(
                        &spill_slot,
                        &(&MemoryLocation::Register(asm::Register::Amd64(Register::Rdx))).into(),
                        &OperandSize::_64,
                        &Origin::default(),
                    );
                    trace!("spill rdx before idiv: spill_slot={:#?}", spill_slot);

                    spill_slot
                };
                let rax_spill_slot = {
                    let spill_slot = self.find_free_spill_slot(&OperandSize::_64);
                    self.emit_store(
                        &spill_slot,
                        &(&MemoryLocation::Register(asm::Register::Amd64(Register::Rax))).into(),
                        &OperandSize::_64,
                        &Origin::default(),
                    );
                    trace!("spill rax before idiv: spill_slot={:#?}", spill_slot);

                    spill_slot
                };

                let lhs = vreg_to_memory_location.get(lhs).unwrap();
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)),
                    &lhs.into(),
                    &OperandSize::_64,
                    &Origin::default(),
                );

                // `idiv` technically divides the 128 bit `rdx:rax` value. Thus, `rdx` is zeroed
                // first to only divide `rax`.
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_R_Imm,
                    operands: vec![
                        Operand::new(
                            &OperandSize::_64,
                            &OperandKind::Register(asm::Register::Amd64(Register::Rdx)),
                        ),
                        Operand::new(&OperandSize::_64, &OperandKind::Immediate(0)),
                    ],
                    origin: ins.origin,
                });
                self.asm.push(Instruction {
                    kind: InstructionKind::IDiv,
                    operands: vec![Operand::from_memory_location(
                        &OperandSize::_64,
                        vreg_to_memory_location.get(rhs).unwrap(),
                    )],
                    origin: ins.origin,
                });

                let dst = vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap();
                // The quotient is now in `rax`.
                // If `dst` should be in `rax`, then nothing to do.
                // Otherwise: need to `mov dst, rax`.
                if dst != &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)) {
                    self.emit_store(
                        dst,
                        &(&MemoryLocation::Register(asm::Register::Amd64(Register::Rax))).into(),
                        &OperandSize::_64,
                        &ins.origin,
                    );
                }

                // Finally: restore rax & rdx.
                {
                    self.emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                        &(&rdx_spill_slot).into(),
                        &OperandSize::_64,
                        &Origin::default(),
                    );
                    trace!("unspill rdx after idiv: spill_slot={:#?}", rdx_spill_slot);

                    self.emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)),
                        &(&rax_spill_slot).into(),
                        &OperandSize::_64,
                        &Origin::default(),
                    );
                    trace!("unspill rax after idiv: spill_slot={:#?}", rax_spill_slot);
                }
            }
            (ir::InstructionKind::Set, Some(ir::Operand::VirtualRegister(lhs)), None) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_R_RM,
                    operands: vec![
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(lhs).unwrap(),
                        ),
                    ],
                    origin: ins.origin,
                });
            }
            (ir::InstructionKind::Set, Some(ir::Operand::Num(num)), None) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_R_Imm,
                    operands: vec![
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::new(&OperandSize::_64, &OperandKind::Immediate(*num)),
                    ],
                    origin: ins.origin,
                });
            }
            (ir::InstructionKind::Set, Some(ir::Operand::Bool(b)), None) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_R_Imm,
                    operands: vec![
                        Operand::from_memory_location(
                            &OperandSize::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::new(
                            &OperandSize::_64,
                            &OperandKind::Immediate(if *b { 1 } else { 0 }),
                        ),
                    ],
                    origin: ins.origin,
                });
            }
            _ => panic!("invalid IR operands"),
        }
    }

    #[warn(unused_results)]
    pub(crate) fn emit(
        &mut self,
        irs: &[ir::Instruction],
        vreg_to_memory_location: &RegisterMapping,
    ) {
        self.asm = Vec::with_capacity(irs.len() * 2);

        for ir in irs {
            self.instruction_selection(ir, vreg_to_memory_location);
        }
    }

    #[warn(unused_results)]
    pub(crate) fn emit_store(
        &mut self,
        dst: &MemoryLocation,
        src: &OperandKind,
        size: &OperandSize,
        origin: &Origin,
    ) {
        match (dst, src) {
            (MemoryLocation::Register(dst_reg), OperandKind::Register(src_reg)) => {
                self.asm.push(Instruction {
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
                    origin: *origin,
                });
            }
            (MemoryLocation::Register(dst_reg), OperandKind::Immediate(src_imm)) => {
                self.asm.push(Instruction {
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
                    origin: *origin,
                });
            }
            (MemoryLocation::Stack(dst_stack), OperandKind::Register(src_reg)) => {
                self.asm.push(Instruction {
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
                    origin: *origin,
                });
            }
            (MemoryLocation::Stack(_), OperandKind::Immediate(_)) => todo!(),
            (MemoryLocation::Register(dst_reg), OperandKind::Stack(_)) => {
                self.asm.push(Instruction {
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
                    origin: *origin,
                });
            }
            (MemoryLocation::Stack(_), OperandKind::Stack(_)) => todo!(),
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
                self.state.insert((&dst.kind).into(), EvalValue::Num(imm));
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
                                .unwrap_or(&EvalValue::Num(0));

                            self.state
                                .entry(MemoryLocation::Register(*dst_reg))
                                .and_modify(|e| {
                                    *e = EvalValue::Num(op_value.as_num() + e.as_num());
                                })
                                .or_insert(EvalValue::Num(0));
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
                                .unwrap_or(&EvalValue::Num(0));

                            self.state
                                .entry(MemoryLocation::Register(*dst_reg))
                                .and_modify(|e| {
                                    *e = EvalValue::Num(op_value.as_num() * e.as_num());
                                })
                                .or_insert(EvalValue::Num(0));
                        }
                        _ => panic!("invalid operand for imul_r_rm instruction"),
                    };
                }
                InstructionKind::IDiv => {
                    assert_eq!(ins.operands.len(), 1);

                    match ins.operands[0].kind {
                        asm::OperandKind::Register(op) => {
                            let divisor = *self.state.get(&MemoryLocation::Register(op)).unwrap();
                            let quotient = self
                                .state
                                .get_mut(&MemoryLocation::Register(asm::Register::Amd64(
                                    Register::Rax,
                                )))
                                .unwrap();

                            let rem = EvalValue::Num(quotient.as_num() % divisor.as_num());
                            *quotient = EvalValue::Num(quotient.as_num() / divisor.as_num());

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
