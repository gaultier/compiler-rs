use std::{io::Write, panic};

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

    Rbp,
    Rsp,
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
    Call,
    Push,
    Pop,
    Ret,
}

pub struct Emitter {
    pub(crate) stack: Stack,
    pub(crate) asm: Vec<Instruction>,
}

impl Emitter {
    pub fn new(initial_stack_offset: isize) -> Self {
        Self {
            stack: Stack::new(initial_stack_offset),
            asm: Vec::new(),
        }
    }

    // TODO: Use a free register if possible.
    fn find_free_spill_slot(&mut self, op_size: &OperandSize) -> MemoryLocation {
        let (size, align) = (op_size.as_bytes_count(), 8); // TODO: Improve.
        let offset = self.stack.new_slot(size, align);
        MemoryLocation::Stack(offset)
    }

    fn instruction_selection(
        &mut self,
        ins: &ir::Instruction,
        vreg_to_memory_location: &RegisterMapping,
    ) {
        match (&ins.kind, &ins.operands.first(), &ins.operands.get(1)) {
            (
                ir::InstructionKind::IAdd,
                Some(ir::Operand::VirtualRegister(lhs)),
                Some(ir::Operand::VirtualRegister(rhs)),
            ) => {
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &vreg_to_memory_location.get(lhs).unwrap().into(),
                    &OperandSize::_64,
                    &ins.origin,
                );
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
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &vreg_to_memory_location.get(lhs).unwrap().into(),
                    &OperandSize::_64,
                    &ins.origin,
                );
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
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)).into(),
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
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)).into(),
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
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                    &OperandKind::Immediate(0),
                    &OperandSize::_64,
                    &ins.origin,
                );
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
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)).into(),
                        &OperandSize::_64,
                        &ins.origin,
                    );
                }

                // Finally: restore rax & rdx.
                {
                    trace!("unspill rdx after idiv: spill_slot={:#?}", &rdx_spill_slot);
                    self.emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                        &rdx_spill_slot.into(),
                        &OperandSize::_64,
                        &Origin::default(),
                    );

                    trace!("unspill rax after idiv: spill_slot={:#?}", rax_spill_slot);
                    self.emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)),
                        &rax_spill_slot.into(),
                        &OperandSize::_64,
                        &Origin::default(),
                    );
                }
            }
            (ir::InstructionKind::Set, Some(ir::Operand::VirtualRegister(lhs)), None) => {
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &vreg_to_memory_location.get(lhs).unwrap().into(),
                    &OperandSize::_64,
                    &ins.origin,
                );
            }
            (ir::InstructionKind::Set, Some(ir::Operand::Num(num)), None) => {
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &OperandKind::Immediate(*num),
                    &OperandSize::_64,
                    &ins.origin,
                );
            }
            (ir::InstructionKind::Set, Some(ir::Operand::Bool(b)), None) => {
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &OperandKind::Immediate(if *b { 1 } else { 0 }),
                    &OperandSize::_64,
                    &ins.origin,
                );
            }
            (
                ir::InstructionKind::FnCall,
                Some(ir::Operand::Fn(fn_name)),
                Some(ir::Operand::VirtualRegister(vreg)),
            ) if fn_name == "println_u64" => {
                let arg = Operand::from_memory_location(
                    &OperandSize::_64,
                    vreg_to_memory_location.get(vreg).unwrap(),
                );

                let spill_slot = self.find_free_spill_slot(&OperandSize::_64);
                self.emit_store(
                    &spill_slot,
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)).into(),
                    &OperandSize::_64,
                    &Origin::default(),
                );
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)),
                    &arg.kind,
                    &OperandSize::_64,
                    &Origin::default(),
                );

                self.asm.push(Instruction {
                    kind: InstructionKind::Call,
                    operands: vec![Operand {
                        operand_size: OperandSize::_64,
                        kind: OperandKind::FnName(fn_name.clone()),
                    }],
                    origin: ins.origin,
                });
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)),
                    &spill_slot.into(),
                    &OperandSize::_64,
                    &Origin::default(),
                );
            }
            x => panic!("invalid IR operands: {:#?}", x),
        }
    }

    pub(crate) fn emit(
        &mut self,
        irs: &[ir::Instruction],
        vreg_to_memory_location: &RegisterMapping,
    ) {
        self.asm = Vec::with_capacity(irs.len() * 2);

        self.asm.push(Instruction {
            kind: InstructionKind::Push,
            operands: vec![Operand {
                operand_size: OperandSize::_64,
                kind: OperandKind::Register(asm::Register::Amd64(Register::Rbp)),
            }],
            origin: Origin::default(),
        });
        self.emit_store(
            &MemoryLocation::Register(asm::Register::Amd64(Register::Rbp)),
            &OperandKind::Register(asm::Register::Amd64(Register::Rsp)),
            &OperandSize::_64,
            &Origin::default(),
        );

        for ir in irs {
            self.instruction_selection(ir, vreg_to_memory_location);
        }

        if !self.stack.is_aligned(16) {
            let delta = self.stack.offset % 16;
            self.stack.offset += delta;
            self.asm.insert(
                2, // Right after: `push rbp; mov rbp, rsp;`.
                Instruction {
                    kind: InstructionKind::Mov_R_Imm,
                    operands: vec![
                        Operand {
                            operand_size: OperandSize::_64,
                            kind: OperandKind::Register(asm::Register::Amd64(Register::Rsp)),
                        },
                        Operand {
                            operand_size: OperandSize::_64,
                            kind: OperandKind::Immediate(delta as i64),
                        },
                    ],
                    origin: Origin::default(),
                },
            );
        }

        // Restore stack.
        self.asm.push(Instruction {
            kind: InstructionKind::Pop,
            operands: vec![Operand {
                operand_size: OperandSize::_64,
                kind: OperandKind::Register(asm::Register::Amd64(Register::Rbp)),
            }],
            origin: Origin::default(),
        });

        // Ret
        self.asm.push(Instruction {
            kind: InstructionKind::Ret,
            operands: vec![],
            origin: Origin::default(),
        });
    }

    pub(crate) fn emit_store(
        &mut self,
        dst: &MemoryLocation,
        src: &OperandKind,
        size: &OperandSize,
        origin: &Origin,
    ) {
        match (dst, src) {
            (_, OperandKind::FnName(_)) => {
                todo!()
            }
            (MemoryLocation::Register(dst_reg), OperandKind::Register(src_reg))
                if dst_reg == src_reg =>
            {
                // noop.
            }
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
                            kind: src.clone(),
                        },
                    ],
                    origin: *origin,
                });
            }
            (MemoryLocation::Stack(dst), OperandKind::Stack(src)) if dst == src => {
                // noop.
            }
            (MemoryLocation::Stack(_), OperandKind::Stack(_)) => todo!(),
        }
    }
}

impl Register {
    pub(crate) fn to_str(self) -> &'static str {
        // TODO: size dependent.

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
            Register::Rsp => "rsp",
            Register::Rbp => "rbp",
        }
    }
}

impl InstructionKind {
    pub(crate) fn to_str(self) -> &'static str {
        // TODO: size.
        match self {
            InstructionKind::Mov_RM_R | InstructionKind::Mov_R_RM | InstructionKind::Mov_R_Imm => {
                "mov"
            }
            InstructionKind::Add_R_RM => "add",
            InstructionKind::IMul_R_RM => "imul",
            InstructionKind::IDiv => "idiv",
            InstructionKind::Lea => "lea",
            InstructionKind::Push => "push",
            InstructionKind::Pop => "pop",

            // Size independent.
            InstructionKind::Call => "call",
            InstructionKind::Ret => "ret",
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

    fn stack_offset(&self) -> isize {
        match self
            .state
            .get(&MemoryLocation::Register(asm::Register::Amd64(
                Register::Rsp,
            )))
            .unwrap()
        {
            EvalValue::Num(n) => *n as isize,
            _ => panic!("invalid rsp value"),
        }
    }

    fn set_stack_offset(&mut self, delta: isize) {
        let val = self
            .state
            .get_mut(&MemoryLocation::Register(asm::Register::Amd64(
                Register::Rsp,
            )))
            .unwrap();
        match *val {
            EvalValue::Num(n) => *val = EvalValue::Num(n + delta as i64),
            _ => panic!("invalid rsp value"),
        };
    }

    fn store(&mut self, dst: &Operand, src: &Operand) {
        match (&dst.kind, &src.kind) {
            (OperandKind::FnName(_), _) => panic!("invalid store to fn name"),
            (_, OperandKind::FnName(_)) => {
                todo!()
            }
            (OperandKind::Register(_), OperandKind::Register(_))
            | (OperandKind::Stack(_), OperandKind::Register(_))
            | (OperandKind::Register(_), OperandKind::Stack(_)) => {
                let value = self
                    .state
                    .get(&(&src.kind).into())
                    .unwrap_or(&EvalValue::Num(0))
                    .clone();
                self.state.insert((&dst.kind).into(), value);
            }
            (OperandKind::Register(_), OperandKind::Immediate(imm))
            | (OperandKind::Stack(_), OperandKind::Immediate(imm)) => {
                self.state.insert((&dst.kind).into(), EvalValue::Num(*imm));
            }
            (OperandKind::Immediate(_), _) => panic!("invalid store destination"),
            (OperandKind::Stack(_), OperandKind::Stack(_)) => panic!("unsupported store"),
        };
    }

    fn load(&mut self, dst: &Operand, src: &Operand) {
        match (&dst.kind, &src.kind) {
            (OperandKind::Register(_), OperandKind::Stack(_)) => {
                let value = self
                    .state
                    .get(&(&src.kind).into())
                    .unwrap_or(&EvalValue::Num(0))
                    .clone();
                self.state.insert((&dst.kind).into(), value);
            }
            _ => panic!("unsupported load"),
        };
    }

    pub fn eval(&mut self, instructions: &[asm::Instruction]) {
        // Assume we are always in `main` or one of its callees and thus
        // `rsp % 16 == -8` since a `call` just happened and thus the
        // return address is on the stack.
        self.state.insert(
            MemoryLocation::Register(asm::Register::Amd64(Register::Rsp)),
            EvalValue::Num(-8),
        );

        for ins in instructions {
            trace!("eval start: {:#?} rsp={}", &ins, self.stack_offset());

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
                            let op_value = self
                                .state
                                .get(&MemoryLocation::Register(op))
                                .unwrap_or(&EvalValue::Num(0))
                                .clone();

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
                            let op_value = self
                                .state
                                .get(&MemoryLocation::Register(op))
                                .unwrap_or(&EvalValue::Num(0))
                                .clone();

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
                            let divisor = self
                                .state
                                .get(&MemoryLocation::Register(op))
                                .unwrap()
                                .clone();
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
                InstructionKind::Call => {
                    // SysV ABI.
                    assert!(self.stack_offset() % 16 == 0, "{}", self.stack_offset());

                    assert_eq!(ins.operands.len(), 1);
                    let fn_name = match &ins.operands.first().unwrap().kind {
                        OperandKind::FnName(fn_name) => fn_name,
                        _ => panic!("invalid call"),
                    };

                    if fn_name != "println_u64" {
                        todo!()
                    }

                    let arg = match self
                        .state
                        .get(&MemoryLocation::Register(asm::Register::Amd64(
                            Register::Rdi,
                        )))
                        .unwrap()
                    {
                        EvalValue::Num(n) => *n,
                        _ => panic!("invalid argument"),
                    };

                    writeln!(&mut std::io::stdout(), "{}", arg).unwrap();
                }
                InstructionKind::Push => {
                    assert_eq!(ins.operands.len(), 1);

                    let op = ins.operands.first().unwrap();

                    let sp = self.stack_offset();
                    self.set_stack_offset(-(op.operand_size.as_bytes_count() as isize));
                    let val = self
                        .state
                        .get(&(&op.kind).into())
                        .unwrap_or(&EvalValue::Num(0))
                        .clone();
                    self.state.insert(MemoryLocation::Stack(sp), val);
                }
                InstructionKind::Pop => {
                    assert_eq!(ins.operands.len(), 1);

                    let op = ins.operands.first().unwrap();
                    match op.kind {
                        OperandKind::Register(_) | OperandKind::Stack(_) => {}
                        _ => panic!("invalid push argument"),
                    };
                    let sp = self.stack_offset();
                    let val = self.state.get(&MemoryLocation::Stack(sp)).unwrap().clone();
                    self.state.insert(op.kind.clone().into(), val);
                    self.set_stack_offset(op.operand_size.as_bytes_count() as isize);
                }
                InstructionKind::Ret => {
                    assert_eq!(ins.operands.len(), 0);
                    assert_eq!(self.stack_offset() % 16, -8);
                    self.set_stack_offset(8); // Pop the return address implicitly.
                }
            }
            trace!("eval end: rsp={}", self.stack_offset());
        }

        // Stack properly reset.
        assert_eq!(self.stack_offset() % 16, 0);
    }
}
