use std::{
    fmt::Display,
    io::{self, Write},
    panic,
};

use log::trace;
use proptest::proptest;
use proptest_derive::Arbitrary;
use serde::Serialize;

use crate::{
    asm::{self, Abi, EvalResult, Stack},
    ir::{self, EvalValue, EvalValueKind},
    origin::Origin,
    register_alloc::{MemoryLocation, RegisterMapping},
    type_checker::Size,
};

#[derive(Serialize, Debug, Clone, Arbitrary)]
pub struct Operand {
    pub size: Size,
    pub kind: OperandKind,
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Arbitrary)]
pub enum Scale {
    _0 = 0,
    _1 = 1,
    _2 = 2,
    _4 = 4,
    _8 = 8,
}

#[derive(Serialize, Debug, Clone, Copy, Arbitrary)]
pub struct EffectiveAddress {
    base: Register,
    index: Option<Register>,
    scale: Scale,
    displacement: i32,
}

#[derive(Serialize, Debug, Clone, Arbitrary)]
pub enum OperandKind {
    Register(Register),
    Immediate(i64),
    EffectiveAddress(EffectiveAddress),
    // For now.
    #[proptest(skip)]
    FnName(String),
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub operands: Vec<Operand>,
    pub origin: Origin,
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Arbitrary)]
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

enum ModRmEncoding {
    Slash0,
    Slash1,
    Slash2,
    Slash3,
    Slash4,
    Slash5,
    Slash6,
    Slash7,
    SlashR,
}

impl Display for Size {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", *self as usize)
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            OperandKind::Register(register) => f.write_str(register.to_str(&self.size)),
            OperandKind::Immediate(n) => write!(f, "{}", n),
            OperandKind::FnName(name) => f.write_str(name),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base,
                index,
                scale,
                displacement,
            }) => {
                f.write_str(self.size.as_asm_addressing_str())?;
                write!(f, " [{}", base.to_str(&self.size))?;
                if let Some(index) = index {
                    write!(f, "  + {}", index.to_str(&self.size))?;
                }
                if *scale != Scale::_0 {
                    write!(f, "  * {}", *scale as u8)?;
                }
                if *displacement > 0 {
                    write!(f, " {:+}", displacement)?;
                }
                write!(f, "]")
            }
        }
    }
}

pub(crate) fn encode(instructions: &[asm::Instruction]) -> Vec<u8> {
    let mut res = Vec::with_capacity(instructions.len() * 5);
    for ins in instructions {
        let asm::Instruction::Amd64(ins) = ins;
        ins.encode(&mut res).unwrap();
    }

    res
}

impl Scale {
    fn to_2_bits(&self) -> u8 {
        match self {
            Scale::_0 | Scale::_1 => 0b00,
            Scale::_2 => 0b01,
            Scale::_4 => 0b10,
            Scale::_8 => 0b11,
        }
    }
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

pub(crate) const GPRS: [Register; 13] = [
    Register::Rax,
    Register::Rbx,
    Register::Rcx,
    Register::Rdx,
    Register::Rdi,
    Register::Rsi,
    Register::R8,
    Register::R9,
    Register::R10,
    // Reserve r11 as scratch register.
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

#[derive(Serialize, Debug, Clone, Copy, Arbitrary)]
#[allow(non_camel_case_types)]
#[repr(u16)]
pub enum InstructionKind {
    Mov,
    Add,
    IMul,
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
    fn find_free_spill_slot(&mut self, op_size: &Size) -> MemoryLocation {
        let (size, align) = (op_size.as_bytes_count(), op_size.as_bytes_count());
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
                Some(ir::Operand {
                    kind: ir::OperandKind::VirtualRegister(lhs),
                    ..
                }),
                Some(ir::Operand {
                    kind: ir::OperandKind::VirtualRegister(rhs),
                    ..
                }),
            ) => {
                let dst_loc = vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap();
                let rhs_loc = vreg_to_memory_location.get(rhs).unwrap();

                self.emit_store(
                    dst_loc,
                    &vreg_to_memory_location.get(lhs).unwrap().into(),
                    &Size::_64,
                    &ins.origin,
                );
                let (kind, rhs_loc) = match (dst_loc, rhs_loc) {
                    (MemoryLocation::Register(_), MemoryLocation::Register(_)) => {
                        (InstructionKind::Add, rhs_loc)
                    }
                    (MemoryLocation::Register(_), MemoryLocation::Stack(_)) => {
                        (InstructionKind::Add, rhs_loc)
                    }
                    (MemoryLocation::Stack(_), MemoryLocation::Register(_)) => {
                        (InstructionKind::Add, rhs_loc)
                    }
                    (MemoryLocation::Stack(_), MemoryLocation::Stack(_)) => {
                        self.emit_store(
                            &MemoryLocation::Register(asm::Register::Amd64(Register::R11)),
                            &((*rhs_loc).into()),
                            &Size::_64,
                            &Origin::new_synth_codegen(),
                        );
                        (
                            InstructionKind::Add,
                            &MemoryLocation::Register(asm::Register::Amd64(Register::R11)),
                        )
                    }
                };

                self.asm.push(Instruction {
                    kind,
                    operands: vec![
                        Operand::from_memory_location(
                            &Size::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::from_memory_location(&Size::_64, rhs_loc),
                    ],
                    origin: ins.origin,
                });
            }
            (
                ir::InstructionKind::IMultiply,
                Some(ir::Operand {
                    kind: ir::OperandKind::VirtualRegister(lhs),
                    ..
                }),
                Some(ir::Operand {
                    kind: ir::OperandKind::VirtualRegister(rhs),
                    ..
                }),
            ) => {
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &vreg_to_memory_location.get(lhs).unwrap().into(),
                    &Size::_64,
                    &ins.origin,
                );
                self.asm.push(Instruction {
                    kind: InstructionKind::IMul,
                    operands: vec![
                        Operand::from_memory_location(
                            &Size::_64,
                            vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                        ),
                        Operand::from_memory_location(
                            &Size::_64,
                            vreg_to_memory_location.get(rhs).unwrap(),
                        ),
                    ],
                    origin: ins.origin,
                });
            }
            (
                ir::InstructionKind::IDivide,
                Some(ir::Operand {
                    kind: ir::OperandKind::VirtualRegister(lhs),
                    ..
                }),
                Some(ir::Operand {
                    kind: ir::OperandKind::VirtualRegister(rhs),
                    ..
                }),
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
                    let spill_slot = self.find_free_spill_slot(&Size::_64);
                    self.emit_store(
                        &spill_slot,
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)).into(),
                        &Size::_64,
                        &Origin::new_synth_codegen(),
                    );
                    trace!("spill rdx before idiv: spill_slot={:#?}", spill_slot);

                    spill_slot
                };
                let rax_spill_slot = {
                    let spill_slot = self.find_free_spill_slot(&Size::_64);
                    self.emit_store(
                        &spill_slot,
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)).into(),
                        &Size::_64,
                        &Origin::new_synth_codegen(),
                    );
                    trace!("spill rax before idiv: spill_slot={:#?}", spill_slot);

                    spill_slot
                };

                let lhs = vreg_to_memory_location.get(lhs).unwrap();
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)),
                    &lhs.into(),
                    &Size::_64,
                    &Origin::new_synth_codegen(),
                );

                // `idiv` technically divides the 128 bit `rdx:rax` value. Thus, `rdx` is zeroed
                // first to only divide `rax`.
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                    &OperandKind::Immediate(0),
                    &Size::_64,
                    &ins.origin,
                );
                self.asm.push(Instruction {
                    kind: InstructionKind::IDiv,
                    operands: vec![Operand::from_memory_location(
                        &Size::_64,
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
                        &Size::_64,
                        &ins.origin,
                    );
                }

                // Finally: restore rax & rdx.
                {
                    trace!("unspill rdx after idiv: spill_slot={:#?}", &rdx_spill_slot);
                    self.emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                        &rdx_spill_slot.into(),
                        &Size::_64,
                        &Origin::new_synth_codegen(),
                    );

                    trace!("unspill rax after idiv: spill_slot={:#?}", rax_spill_slot);
                    self.emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)),
                        &rax_spill_slot.into(),
                        &Size::_64,
                        &Origin::new_synth_codegen(),
                    );
                }
            }
            (
                ir::InstructionKind::Set,
                Some(ir::Operand {
                    kind: ir::OperandKind::VirtualRegister(lhs),
                    ..
                }),
                None,
            ) => {
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &vreg_to_memory_location.get(lhs).unwrap().into(),
                    &Size::_64,
                    &ins.origin,
                );
            }
            (
                ir::InstructionKind::Set,
                Some(ir::Operand {
                    kind: ir::OperandKind::Num(num),
                    ..
                }),
                None,
            ) => {
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &OperandKind::Immediate(*num),
                    &ins.typ.size,
                    &ins.origin,
                );
            }
            (
                ir::InstructionKind::Set,
                Some(ir::Operand {
                    kind: ir::OperandKind::Bool(b),
                    ..
                }),
                None,
            ) => {
                self.emit_store(
                    vreg_to_memory_location.get(&ins.res_vreg.unwrap()).unwrap(),
                    &OperandKind::Immediate(if *b { 1 } else { 0 }),
                    &Size::_8,
                    &ins.origin,
                );
            }
            (
                ir::InstructionKind::FnCall,
                Some(ir::Operand {
                    kind: ir::OperandKind::Fn(fn_name),
                    ..
                }),
                Some(ir::Operand {
                    kind: ir::OperandKind::VirtualRegister(vreg),
                    ..
                }),
            ) if fn_name == "println_u64" => {
                let arg = Operand::from_memory_location(
                    &Size::_64,
                    vreg_to_memory_location.get(vreg).unwrap(),
                );

                let spill_slot = self.find_free_spill_slot(&Size::_64);
                self.emit_store(
                    &spill_slot,
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)).into(),
                    &Size::_64,
                    &Origin::new_synth_codegen(),
                );
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)),
                    &arg.kind,
                    &Size::_64,
                    &Origin::new_synth_codegen(),
                );

                self.asm.push(Instruction {
                    kind: InstructionKind::Call,
                    operands: vec![Operand {
                        size: Size::_64,
                        kind: OperandKind::FnName(fn_name.clone()),
                    }],
                    origin: ins.origin,
                });
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)),
                    &spill_slot.into(),
                    &Size::_64,
                    &Origin::new_synth_codegen(),
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
                size: Size::_64,
                kind: OperandKind::Register(Register::Rbp),
            }],
            origin: Origin::new_synth_codegen(),
        });
        self.emit_store(
            &MemoryLocation::Register(asm::Register::Amd64(Register::Rbp)),
            &OperandKind::Register(Register::Rsp),
            &Size::_64,
            &Origin::new_synth_codegen(),
        );

        // Always align stack to 16 bytes so that function calls can be made.
        // Technically it's not necessary in leaf functions but we do it anyway.
        let delta = self.stack.offset % 16;
        self.stack.offset += delta;
        let stack_offset_frame = self.stack.offset as i64;

        if stack_offset_frame != 0 {
            self.asm.push(Instruction {
                kind: InstructionKind::Add,
                operands: vec![
                    Operand {
                        size: Size::_64,
                        kind: OperandKind::Register(Register::Rsp),
                    },
                    Operand {
                        size: Size::_64,
                        kind: OperandKind::Immediate(stack_offset_frame),
                    },
                ],
                origin: Origin::new_synth_codegen(),
            });
        }

        for ir in irs {
            self.instruction_selection(ir, vreg_to_memory_location);
        }

        // Restore stack.
        if stack_offset_frame != 0 {
            self.asm.push(Instruction {
                kind: InstructionKind::Add,
                operands: vec![
                    Operand {
                        size: Size::_64,
                        kind: OperandKind::Register(Register::Rsp),
                    },
                    Operand {
                        size: Size::_64,
                        kind: OperandKind::Immediate(-(stack_offset_frame)),
                    },
                ],
                origin: Origin::new_synth_codegen(),
            });
        }
        self.asm.push(Instruction {
            kind: InstructionKind::Pop,
            operands: vec![Operand {
                size: Size::_64,
                kind: OperandKind::Register(Register::Rbp),
            }],
            origin: Origin::new_synth_codegen(),
        });

        // Ret
        self.asm.push(Instruction {
            kind: InstructionKind::Ret,
            operands: vec![],
            origin: Origin::new_synth_codegen(),
        });
    }

    pub(crate) fn emit_store(
        &mut self,
        dst: &MemoryLocation,
        src: &OperandKind,
        size: &Size,
        origin: &Origin,
    ) {
        match (dst, src) {
            (_, OperandKind::FnName(_)) => {
                todo!()
            }
            (
                MemoryLocation::Register(asm::Register::Amd64(dst_reg)),
                OperandKind::Register(src_reg),
            ) if dst_reg == src_reg => {
                // noop.
            }
            (
                MemoryLocation::Register(asm::Register::Amd64(dst_reg)),
                OperandKind::Register(src_reg),
            ) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![
                        Operand {
                            size: *size,
                            kind: OperandKind::Register(*dst_reg),
                        },
                        Operand {
                            size: *size,
                            kind: OperandKind::Register(*src_reg),
                        },
                    ],
                    origin: *origin,
                });
            }
            (
                MemoryLocation::Register(asm::Register::Amd64(dst_reg)),
                OperandKind::Immediate(src_imm),
            ) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![
                        Operand {
                            size: *size,
                            kind: OperandKind::Register(*dst_reg),
                        },
                        Operand {
                            size: *size,
                            kind: OperandKind::Immediate(*src_imm),
                        },
                    ],
                    origin: *origin,
                });
            }
            (MemoryLocation::Stack(_), OperandKind::Register(src_reg)) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![
                        Operand {
                            size: *size,
                            kind: dst.into(),
                        },
                        Operand {
                            size: *size,
                            kind: OperandKind::Register(*src_reg),
                        },
                    ],
                    origin: *origin,
                });
            }
            (MemoryLocation::Stack(off), OperandKind::Immediate(imm)) => {
                if *imm > i32::MAX as i64 {
                    todo!();
                }

                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![
                        Operand {
                            size: *size,
                            kind: OperandKind::EffectiveAddress(EffectiveAddress {
                                base: Register::Rsp,
                                index: None,
                                scale: Scale::_0,
                                displacement: (*off).try_into().unwrap(),
                            }),
                        },
                        Operand {
                            size: *size,
                            kind: src.clone(),
                        },
                    ],
                    origin: *origin,
                });
            }
            (
                MemoryLocation::Register(asm::Register::Amd64(dst_reg)),
                OperandKind::EffectiveAddress(_),
            ) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![
                        Operand {
                            size: *size,
                            kind: OperandKind::Register(*dst_reg),
                        },
                        Operand {
                            size: *size,
                            kind: src.clone(),
                        },
                    ],
                    origin: *origin,
                });
            }
            (
                MemoryLocation::Stack(dst),
                OperandKind::EffectiveAddress(EffectiveAddress {
                    base: Register::Rsp,
                    index: None,
                    scale: Scale::_0,
                    displacement,
                }),
            ) if *dst == (*displacement as isize) => {
                // noop.
            }
            (MemoryLocation::Stack(_), OperandKind::EffectiveAddress(_)) => todo!(),
        }
    }
}

impl Register {
    fn to_3_bits(&self) -> u8 {
        let res = match self {
            Register::Rax => 0b000,
            Register::Rbx => 0b011,
            Register::Rcx => 0b001,
            Register::Rdx => 0b010,
            Register::Rdi => 0b111,
            Register::Rsi => 0b110,
            Register::R8 => 0b000,
            Register::R9 => 0b001,
            Register::R10 => 0b010,
            Register::R11 => 0b011,
            Register::R12 => 0b100,
            Register::R13 => 0b101,
            Register::R14 => 0b110,
            Register::R15 => 0b111,
            Register::Rbp => 0b101,
            Register::Rsp => 0b100,
        };
        assert!(res <= 0b111);
        res
    }

    pub fn is_extended(&self) -> bool {
        match self {
            Register::Rax => false,
            Register::Rbx => false,
            Register::Rcx => false,
            Register::Rdx => false,
            Register::Rdi => false,
            Register::Rsi => false,
            Register::R8 => true,
            Register::R9 => true,
            Register::R10 => true,
            Register::R11 => true,
            Register::R12 => true,
            Register::R13 => true,
            Register::R14 => true,
            Register::R15 => true,
            Register::Rbp => false,
            Register::Rsp => false,
        }
    }

    pub(crate) fn to_str(self, size: &Size) -> &'static str {
        match (self, size) {
            (Register::Rax, Size::_8) => "al",
            (Register::Rax, Size::_16) => "ax",
            (Register::Rax, Size::_32) => "eax",
            (Register::Rax, Size::_64) => "rax",
            (Register::Rbx, Size::_8) => "bl",
            (Register::Rbx, Size::_16) => "bx",
            (Register::Rbx, Size::_32) => "ebx",
            (Register::Rbx, Size::_64) => "rbx",
            (Register::Rcx, Size::_8) => "cl",
            (Register::Rcx, Size::_16) => "cx",
            (Register::Rcx, Size::_32) => "ecx",
            (Register::Rcx, Size::_64) => "rcx",
            (Register::Rdx, Size::_8) => "dl",
            (Register::Rdx, Size::_16) => "dx",
            (Register::Rdx, Size::_32) => "edx",
            (Register::Rdx, Size::_64) => "rdx",
            (Register::Rdi, Size::_8) => "dil",
            (Register::Rdi, Size::_16) => "di",
            (Register::Rdi, Size::_32) => "edi",
            (Register::Rdi, Size::_64) => "rdi",
            (Register::Rsi, Size::_8) => "sil",
            (Register::Rsi, Size::_16) => "si",
            (Register::Rsi, Size::_32) => "esi",
            (Register::Rsi, Size::_64) => "rsi",
            (Register::R8, Size::_8) => "r8b",
            (Register::R8, Size::_16) => "r8w",
            (Register::R8, Size::_32) => "r8d",
            (Register::R8, Size::_64) => "r8",
            (Register::R9, Size::_8) => "r9b",
            (Register::R9, Size::_16) => "r9w",
            (Register::R9, Size::_32) => "r9d",
            (Register::R9, Size::_64) => "r9",
            (Register::R10, Size::_8) => "r10b",
            (Register::R10, Size::_16) => "r10w",
            (Register::R10, Size::_32) => "r10d",
            (Register::R10, Size::_64) => "r10",
            (Register::R11, Size::_8) => "r11b",
            (Register::R11, Size::_16) => "r11w",
            (Register::R11, Size::_32) => "r11d",
            (Register::R11, Size::_64) => "r11",
            (Register::R12, Size::_8) => "r12b",
            (Register::R12, Size::_16) => "r12w",
            (Register::R12, Size::_32) => "r12d",
            (Register::R12, Size::_64) => "r12",
            (Register::R13, Size::_8) => "r13b",
            (Register::R13, Size::_16) => "r13w",
            (Register::R13, Size::_32) => "r13d",
            (Register::R13, Size::_64) => "r13",
            (Register::R14, Size::_8) => "r14b",
            (Register::R14, Size::_16) => "r14w",
            (Register::R14, Size::_32) => "r14d",
            (Register::R14, Size::_64) => "r14",
            (Register::R15, Size::_8) => "r15b",
            (Register::R15, Size::_16) => "r15w",
            (Register::R15, Size::_32) => "r15d",
            (Register::R15, Size::_64) => "r15",
            (Register::Rsp, Size::_8) => "spl",
            (Register::Rsp, Size::_16) => "sp",
            (Register::Rsp, Size::_32) => "esp",
            (Register::Rsp, Size::_64) => "rsp",
            (Register::Rbp, Size::_8) => "bpl",
            (Register::Rbp, Size::_16) => "bp",
            (Register::Rbp, Size::_32) => "ebp",
            (Register::Rbp, Size::_64) => "rbp",
            (_, Size::_0) => panic!("zero size for register"),
        }
    }
}

impl InstructionKind {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            InstructionKind::Mov => "mov",
            InstructionKind::Add => "add",
            InstructionKind::IMul => "imul",
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

impl Instruction {
    // w: register is extended (r8-r15) OR manipulates operand size
    // r: modr/m reg field is extended
    // x: the index field in SIB is extended
    // b: modr/m r/m OR the base field in SIB OR the opcode reg field used for accessing GPRs is extended
    fn encode_rex<W: Write>(wr: &mut W, w: bool, r: bool, x: bool, b: bool) -> std::io::Result<()> {
        let default = 0b0100_0000;
        let mut res = default;

        if w {
            // W
            res |= 0b0000_1000;
        }

        if r {
            // R
            res |= 0b0000_0100;
        }

        if x {
            // X
            res |= 0b0000_0010;
        }

        if b {
            // B
            res |= 0b0000_0001;
        }

        // > A REX prefix is necessary only if an instruction references
        // > one of the extended registers or one of the byte registers SPL, BPL, SIL,
        // DIL;
        // > or uses a 64-bit operand.
        if res != default {
            wr.write_all(&[res])?;
        }
        Ok(())
    }

    fn encode_rex_from_operand<W: Write>(w: &mut W, op: &Operand) -> std::io::Result<()> {
        match op.kind {
            OperandKind::Register(reg) => {
                Instruction::encode_rex(w, op.size == Size::_64, reg.is_extended(), false, false)?;
            }
            OperandKind::EffectiveAddress(addr) => {
                Instruction::encode_rex(
                    w,
                    op.size == Size::_64,
                    false,
                    addr.index.map(|x| x.is_extended()).unwrap_or_default(),
                    addr.base.is_extended(),
                )?;
            }

            _ => {}
        }
        Ok(())
    }

    // Format: `mod (2 bits) | reg (3 bits) | rm (3bits)`.
    fn encode_modrm(encoding: ModRmEncoding, op_rm: &Operand, op_reg: Option<Register>) -> u8 {
        let reg: u8 = match encoding {
            ModRmEncoding::Slash0 => 0,
            ModRmEncoding::Slash1 => 1,
            ModRmEncoding::Slash2 => 2,
            ModRmEncoding::Slash3 => 3,
            ModRmEncoding::Slash4 => 4,
            ModRmEncoding::Slash5 => 5,
            ModRmEncoding::Slash6 => 6,
            ModRmEncoding::Slash7 => 7,
            ModRmEncoding::SlashR => op_reg.unwrap().to_3_bits(),
        };
        assert!(reg <= 0b111); // Fits in 3 bits.

        let (mod_, rm): (u8, u8) = match op_rm.kind {
            OperandKind::Register(reg) => (0b11, reg.to_3_bits()),
            OperandKind::Immediate(_) => (0b00, 0b101),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rax,
                index: None,
                scale: Scale::_0,
                displacement: 0,
            }) => (0b00, 0b000),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rcx,
                index: None,
                scale: Scale::_0,
                displacement: 0,
            }) => (0b00, 0b001),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rdx,
                index: None,
                scale: Scale::_0,
                displacement: 0,
            }) => (0b00, 0b010),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rbx,
                index: None,
                scale: Scale::_0,
                displacement: 0,
            }) => (0b00, 0b011),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rsi,
                index: None,
                scale: Scale::_0,
                displacement: 0,
            }) => (0b00, 0b110),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rdi,
                index: None,
                scale: Scale::_0,
                displacement: 0,
            }) => (0b00, 0b111),
            // TODO: case for disp32
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rax,
                index: None,
                scale: Scale::_0,
                displacement,
            }) if displacement <= i8::MAX as i32 => (0b01, 0b000),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rcx,
                index: None,
                scale: Scale::_0,
                displacement,
            }) if displacement <= i8::MAX as i32 => (0b01, 0b001),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rdx,
                index: None,
                scale: Scale::_0,
                displacement,
            }) if displacement <= i8::MAX as i32 => (0b01, 0b010),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rbx,
                index: None,
                scale: Scale::_0,
                displacement,
            }) if displacement <= i8::MAX as i32 => (0b01, 0b011),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rbp,
                index: None,
                scale: Scale::_0,
                displacement,
            }) if displacement <= i8::MAX as i32 => (0b01, 0b101),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rsi,
                index: None,
                scale: Scale::_0,
                displacement,
            }) if displacement <= i8::MAX as i32 => (0b01, 0b110),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rax,
                index: None,
                scale: Scale::_0,
                ..
            }) => (0b10, 0b000),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rcx,
                index: None,
                scale: Scale::_0,
                ..
            }) => (0b10, 0b001),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rdx,
                index: None,
                scale: Scale::_0,
                ..
            }) => (0b10, 0b010),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rbx,
                index: None,
                scale: Scale::_0,
                ..
            }) => (0b10, 0b011),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rbp,
                index: None,
                scale: Scale::_0,
                ..
            }) => (0b10, 0b101),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rsi,
                index: None,
                scale: Scale::_0,
                ..
            }) => (0b10, 0b110),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rdi,
                index: None,
                scale: Scale::_0,
                ..
            }) => (0b10, 0b111),

            OperandKind::EffectiveAddress(EffectiveAddress {
                displacement: 0, ..
            }) => (0b00, 0b100),
            OperandKind::EffectiveAddress(EffectiveAddress { displacement, .. })
                if displacement <= i8::MAX as i32 =>
            {
                (0b01, 0b100)
            }
            OperandKind::EffectiveAddress(_) => (0b10, 0b100),

            OperandKind::FnName(_) => todo!(),
        };

        assert!(mod_ <= 0b11); // Fits in 2 bits.
        assert!(rm <= 0b111); // Fits in 3 bits.

        mod_ << 6 | reg << 3 | rm
    }

    // Encoding: `Scale(2 bits) | Index(3 bits) | Base (3bits)`.
    fn encode_sib<W: Write>(w: &mut W, addr: &EffectiveAddress, modrm: u8) -> std::io::Result<()> {
        let is_sib_required = matches!(
            // (mod, rm)
            (modrm >> 6, modrm & 0b111),
            (0b00, 0b100) | (0b01, 0b100) | (0b10, 0b100)
        );

        if is_sib_required {
            let scale = addr.scale.to_2_bits() << 6;
            let index = addr.index.map(|x| x.to_3_bits()).unwrap_or_default() << 3;

            let base = addr.base.to_3_bits();
            let sib = scale | index | base;
            w.write_all(&[sib])?;
        }

        // Displacement.
        if addr.displacement > 0 || addr.can_base_be_mistaken_for_rel_addressing() {
            if let Ok(disp) = i8::try_from(addr.displacement) {
                w.write_all(&disp.to_le_bytes())?;
            } else {
                w.write_all(&addr.displacement.to_le_bytes())?;
            }
        }

        Ok(())
    }

    pub(crate) fn encode<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        if let Some(Operand {
            size: Size::_16, ..
        }) = self.operands.first()
        {
            w.write_all(&[0x66])?; // 16 bits prefix.
        }

        match self.kind {
            InstructionKind::Mov => {
                if self.operands.len() != 2 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let lhs = &self.operands[0];
                let rhs = &self.operands[1];

                match (&lhs.kind, &rhs.kind, lhs.size) {
                    // mov rm, r
                    (_, OperandKind::Register(reg), Size::_8) if lhs.is_rm() => {
                        Instruction::encode_rex(w, false, reg.is_extended(), false, false)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x88, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (_, OperandKind::Register(reg), Size::_16 | Size::_32) if lhs.is_rm() => {
                        Instruction::encode_rex(w, false, reg.is_extended(), false, false)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x89, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (_, OperandKind::Register(reg), Size::_64) if lhs.is_rm() => {
                        Instruction::encode_rex(w, true, reg.is_extended(), false, false)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x89, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }

                    // mov r, rm
                    (OperandKind::Register(reg), _, Size::_8) if lhs.is_rm() => {
                        Instruction::encode_rex(w, false, reg.is_extended(), false, false)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(*reg));
                        w.write_all(&[0x8A, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (OperandKind::Register(reg), _, Size::_16 | Size::_32) if lhs.is_rm() => {
                        Instruction::encode_rex(w, false, reg.is_extended(), false, false)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(*reg));
                        w.write_all(&[0x8B, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (OperandKind::Register(reg), _, Size::_64) if lhs.is_rm() => {
                        Instruction::encode_rex(w, true, reg.is_extended(), false, false)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(*reg));
                        w.write_all(&[0x8B, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }

                    // mov rm, imm
                    (_, OperandKind::Immediate(imm), Size::_8) if lhs.is_rm() => {
                        Instruction::encode_rex_from_operand(w, lhs)?;

                        let imm = i8::try_from(*imm).unwrap();
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0xC6, modrm])?;
                        w.write_all(&imm.to_le_bytes())?;
                    }
                    (_, OperandKind::Immediate(imm), Size::_16) if lhs.is_rm() => {
                        Instruction::encode_rex_from_operand(w, lhs)?;

                        let imm = i16::try_from(*imm).unwrap();
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0xC7, modrm])?;
                        w.write_all(&imm.to_le_bytes())?;
                    }
                    (_, OperandKind::Immediate(imm), Size::_32) if lhs.is_rm() => {
                        Instruction::encode_rex_from_operand(w, lhs)?;

                        let imm = i32::try_from(*imm).unwrap();
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0xC7, modrm])?;
                        w.write_all(&imm.to_le_bytes())?;
                    }
                    (_, OperandKind::Immediate(imm), Size::_64) if lhs.is_rm() => {
                        Instruction::encode_rex_from_operand(w, lhs)?;

                        let imm = i32::try_from(*imm).unwrap();
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0xC7, modrm])?;
                        w.write_all(&imm.to_le_bytes())?;
                    }

                    x => unimplemented!("{:?}", x),
                }
                Ok(())
            }
            InstructionKind::Add => {
                if self.operands.len() != 2 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let lhs = &self.operands[0];
                let rhs = &self.operands[1];
                if lhs.size == Size::_0 || lhs.size != rhs.size {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                match (&lhs.kind, &rhs.kind, lhs.size) {
                    (_, OperandKind::Immediate(imm), Size::_8) if lhs.is_rm() => {
                        Instruction::encode_rex_from_operand(w, lhs)?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0x80, modrm])?;
                        let imm = i8::try_from(*imm).unwrap();
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        w.write_all(&imm.to_le_bytes())?;
                    }
                    (_, OperandKind::Immediate(imm), Size::_16 | Size::_32) if lhs.is_rm() => {
                        Instruction::encode_rex_from_operand(w, lhs)?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0x81, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        let imm = i16::try_from(*imm).unwrap();

                        w.write_all(&imm.to_le_bytes())?;
                    }
                    (_, OperandKind::Immediate(imm), Size::_64) if lhs.is_rm() => {
                        Instruction::encode_rex_from_operand(w, lhs)?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0x83, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        w.write_all(&imm.to_le_bytes())?;
                    }
                    (_, OperandKind::Register(reg), Size::_8) if lhs.is_rm() => {
                        Instruction::encode_rex_from_operand(w, lhs)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x00, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (_, OperandKind::Register(reg), Size::_16 | Size::_32 | Size::_64)
                        if lhs.is_rm() =>
                    {
                        Instruction::encode_rex_from_operand(w, lhs)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x01, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    _ => unimplemented!(),
                }
                Ok(())
            }
            InstructionKind::IMul => {
                if self.operands.len() != 2 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let lhs = &self.operands[0];
                let rhs = &self.operands[1];
                if lhs.size == Size::_0 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                if lhs.size == Size::_8 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                if lhs.size != rhs.size {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                match (&lhs.kind, &rhs.kind, lhs.size) {
                    (OperandKind::Register(reg), _, Size::_16)
                    | (OperandKind::Register(reg), _, Size::_32)
                        if rhs.is_rm() =>
                    {
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(*reg));
                        w.write_all(&[0x0f, 0xaf, modrm])?;
                        if let Some(addr) = rhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (OperandKind::Register(reg), _, Size::_64) if rhs.is_rm() => {
                        Instruction::encode_rex(w, true, reg.is_extended(), false, false)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(*reg));
                        w.write_all(&[0x0f, 0xaf, modrm])?;
                        if let Some(addr) = rhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    _ => return Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
                Ok(())
            }
            InstructionKind::IDiv => {
                if self.operands.len() != 1 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let op = self.operands.first().unwrap();
                if !op.is_rm() {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let modrm = Instruction::encode_modrm(ModRmEncoding::Slash7, op, None);

                match (&op.kind, op.size) {
                    (OperandKind::Register(reg), Size::_8) => {
                        Instruction::encode_rex(w, false, false, false, reg.is_extended())?;
                        w.write_all(&[0xf6])?;
                        w.write_all(&[modrm])
                    }

                    (OperandKind::EffectiveAddress(addr), Size::_8) => {
                        Instruction::encode_rex(
                            w,
                            false,
                            false,
                            addr.index.map(|x| x.is_extended()).unwrap_or_default(),
                            addr.base.is_extended(),
                        )?;
                        w.write_all(&[0xf6])?;
                        w.write_all(&[modrm])?;
                        Instruction::encode_sib(w, addr, modrm)
                    }
                    (OperandKind::Register(_), Size::_16 | Size::_32) => {
                        w.write_all(&[0xf7])?;
                        w.write_all(&[modrm])
                    }
                    (OperandKind::Register(reg), Size::_64) => {
                        Instruction::encode_rex(w, true, false, false, reg.is_extended())?;
                        w.write_all(&[modrm])
                    }
                    (OperandKind::EffectiveAddress(addr), Size::_64) => {
                        Instruction::encode_rex(
                            w,
                            true,
                            false,
                            addr.index.map(|x| x.is_extended()).unwrap_or_default(),
                            addr.base.is_extended(),
                        )?;
                        w.write_all(&[0xf7])?;
                        w.write_all(&[modrm])?;
                        Instruction::encode_sib(w, addr, modrm)
                    }
                    _ => return Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
            }
            InstructionKind::Lea => {
                if self.operands.len() != 2 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let lhs = self.operands.first().unwrap();
                let rhs = self.operands.get(1).unwrap();

                if lhs.size == Size::_8 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                if !lhs.is_reg() {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                if !rhs.is_effective_address() {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let reg = lhs.as_reg().unwrap();
                let addr = rhs.as_effective_address().unwrap();

                Instruction::encode_rex(
                    w,
                    lhs.size == Size::_64,
                    reg.is_extended(),
                    addr.index.map(|x| x.is_extended()).unwrap_or_default(),
                    addr.base.is_extended(),
                )?;

                let opcode = 0x8d;
                w.write_all(&[opcode])?;

                let modrm = Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(reg));
                w.write_all(&[modrm])?;

                Instruction::encode_sib(w, &addr, modrm)
            }
            InstructionKind::Call => {
                let displacement: i32 = 0; // FIXME: resolve offset with linker.
                w.write_all(&[0xe8])?; // Call near.
                w.write_all(&displacement.to_le_bytes())
            }
            InstructionKind::Push => {
                if self.operands.len() != 1 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let op = self.operands.first().unwrap();
                if op.size != Size::_64 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }
                match op.kind {
                    OperandKind::Register(reg) => {
                        Instruction::encode_rex(w, false, false, false, reg.is_extended())?;
                        w.write_all(&[0x50 | reg.to_3_bits()])
                    }
                    OperandKind::Immediate(imm) => {
                        if let Ok(imm) = i8::try_from(imm) {
                            w.write_all(&[0x6A])?;
                            w.write_all(&imm.to_le_bytes())?;
                        } else if let Ok(imm) = i16::try_from(imm) {
                            w.write_all(&[0x68])?;
                            w.write_all(&imm.to_le_bytes())?;
                        } else {
                            w.write_all(&[0x68])?;
                            w.write_all(&imm.to_le_bytes())?;
                        }
                        Ok(())
                    }
                    OperandKind::EffectiveAddress(addr) => {
                        if op.size == Size::_0 || op.size == Size::_8 {
                            return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                        }

                        Instruction::encode_rex(
                            w,
                            false, // `push` is 64 bits only.
                            false,
                            addr.index.map(|x| x.is_extended()).unwrap_or_default(),
                            addr.base.is_extended(),
                        )?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash6, op, None);
                        w.write_all(&[0xff, modrm])?;
                        Instruction::encode_sib(w, &addr, modrm)
                    }
                    _ => return Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
            }
            InstructionKind::Pop => {
                if self.operands.len() != 1 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let op = self.operands.first().unwrap();
                if op.size != Size::_64 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }
                match op.kind {
                    OperandKind::Register(reg) => {
                        Instruction::encode_rex(w, false, false, false, reg.is_extended())?;

                        w.write_all(&[0x58 | reg.to_3_bits()])
                    }
                    OperandKind::EffectiveAddress(addr) => {
                        if op.size == Size::_0 || op.size == Size::_8 {
                            return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                        }

                        Instruction::encode_rex(
                            w,
                            false, // `pop` is 64 bits only.
                            false,
                            addr.index.map(|x| x.is_extended()).unwrap_or_default(),
                            addr.base.is_extended(),
                        )?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, op, None);
                        w.write_all(&[0x8f, modrm])?;
                        Instruction::encode_sib(w, &addr, modrm)
                    }
                    _ => return Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
            }
            InstructionKind::Ret => {
                w.write_all(&[0xC3]) // Near return.
            }
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
            .kind
        {
            EvalValueKind::Num(n) => n as isize,
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
        match val {
            EvalValue {
                kind: EvalValueKind::Num(n),
                ..
            } => *val = EvalValue::new_int(*n + delta as i64),
            _ => panic!("invalid rsp value"),
        };
    }

    fn store(&mut self, dst: &Operand, src: &Operand) {
        assert_eq!(dst.size, src.size);

        match (&dst.kind, &src.kind) {
            (OperandKind::FnName(_), _) => panic!("invalid store to fn name"),
            (_, OperandKind::FnName(_)) => {
                todo!()
            }
            (OperandKind::Register(_), OperandKind::Register(_))
            | (OperandKind::EffectiveAddress(_), OperandKind::Register(_))
            | (OperandKind::Register(_), OperandKind::EffectiveAddress(_)) => {
                let value = self
                    .state
                    .get(&(&src.kind).into())
                    .unwrap_or(&EvalValue::new_int(0))
                    .clone();
                self.state.insert((&dst.kind).into(), value);
            }
            (OperandKind::Register(_), OperandKind::Immediate(imm))
            | (OperandKind::EffectiveAddress(_), OperandKind::Immediate(imm)) => {
                self.state
                    .insert((&dst.kind).into(), EvalValue::new_int(*imm));
            }
            (OperandKind::Immediate(_), _) => panic!("invalid store destination"),
            (OperandKind::EffectiveAddress(_), OperandKind::EffectiveAddress(_)) => {
                panic!("unsupported store")
            }
        };
    }

    fn load(&mut self, dst: &Operand, src: &Operand) {
        assert_eq!(dst.size, src.size);

        match (&dst.kind, &src.kind) {
            (OperandKind::Register(_), OperandKind::EffectiveAddress(_)) => {
                let value = self
                    .state
                    .get(&(&src.kind).into())
                    .unwrap_or(&EvalValue::new_int(0))
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
            EvalValue::new_int(-8),
        );
        // TODO: Use an 'undefined' value for the default value and treat reading this value as a
        // fatal error.

        for ins in instructions {
            trace!("eval start: {:#?} rsp={}", &ins, self.stack_offset());

            let asm::Instruction::Amd64(ins) = ins;

            match ins.kind {
                InstructionKind::Mov => {
                    assert_eq!(ins.operands.len(), 2);
                    self.store(&ins.operands[0], &ins.operands[1]);
                }
                InstructionKind::Add => {
                    assert_eq!(ins.operands.len(), 2);
                    let size = ins.operands[0].size;
                    assert_eq!(size, ins.operands[1].size);

                    assert!(ins.operands[0].is_rm());
                    let dst: MemoryLocation = (&ins.operands[0].kind).into();

                    let src: MemoryLocation = (&ins.operands[1].kind).into();

                    let op_value = self
                        .state
                        .get(&src)
                        .unwrap_or(&EvalValue::new_int(0))
                        .clone();

                    self.state
                        .entry(dst)
                        .and_modify(|e| {
                            *e = EvalValue::new_int(op_value.as_num() + e.as_num());
                        })
                        .or_insert(EvalValue::new_int(0));
                }
                InstructionKind::IMul => {
                    assert_eq!(ins.operands.len(), 2);
                    let size = ins.operands[0].size;
                    assert_eq!(size, ins.operands[1].size);

                    let dst_reg = match &ins.operands[0] {
                        Operand {
                            kind: OperandKind::Register(reg),
                            ..
                        } => reg,
                        _ => panic!("invalid dst"),
                    };

                    match ins.operands[1].kind {
                        OperandKind::Register(reg) => {
                            let op_value = self
                                .state
                                .get(&MemoryLocation::Register(asm::Register::Amd64(reg)))
                                .unwrap_or(&EvalValue::new_int(0))
                                .clone();

                            self.state
                                .entry(MemoryLocation::Register(asm::Register::Amd64(*dst_reg)))
                                .and_modify(|e| {
                                    *e = EvalValue::new_int(op_value.as_num() * e.as_num());
                                })
                                .or_insert(EvalValue::new_int(0));
                        }
                        _ => panic!("invalid operand for imul_r_rm instruction"),
                    };
                }
                InstructionKind::IDiv => {
                    assert_eq!(ins.operands.len(), 1);
                    match ins.operands[0].kind {
                        OperandKind::Register(reg) => {
                            let divisor = self
                                .state
                                .get(&MemoryLocation::Register(asm::Register::Amd64(reg)))
                                .unwrap()
                                .clone();
                            let quotient = self
                                .state
                                .get_mut(&MemoryLocation::Register(asm::Register::Amd64(
                                    Register::Rax,
                                )))
                                .unwrap();

                            assert_eq!(divisor.size(), quotient.size());

                            let rem = EvalValue::new_int(quotient.as_num() % divisor.as_num());
                            *quotient = EvalValue::new_int(quotient.as_num() / divisor.as_num());

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

                    let arg = self
                        .state
                        .get(&MemoryLocation::Register(asm::Register::Amd64(
                            Register::Rdi,
                        )))
                        .unwrap()
                        .as_num();

                    writeln!(&mut std::io::stdout(), "{}", arg).unwrap();
                }
                InstructionKind::Push => {
                    assert_eq!(ins.operands.len(), 1);

                    let op = ins.operands.first().unwrap();
                    assert_eq!(op.size, Size::_64);

                    let sp = self.stack_offset();
                    self.set_stack_offset(-(op.size.as_bytes_count() as isize));
                    let val = self
                        .state
                        .get(&(&op.kind).into())
                        .unwrap_or(&EvalValue::new_int(0))
                        .clone();
                    self.state.insert(MemoryLocation::Stack(sp), val);
                }
                InstructionKind::Pop => {
                    assert_eq!(ins.operands.len(), 1);

                    let op = ins.operands.first().unwrap();
                    assert_eq!(op.size, Size::_64);

                    match op.kind {
                        OperandKind::Register(_) | OperandKind::EffectiveAddress(_) => {}
                        _ => panic!("invalid push argument"),
                    };
                    let sp = self.stack_offset();
                    let val = self
                        .state
                        .get(&MemoryLocation::Stack(sp))
                        .unwrap_or(&EvalValue::new_int(0))
                        .clone();
                    self.state.insert(op.kind.clone().into(), val);
                    self.set_stack_offset(op.size.as_bytes_count() as isize);
                }
                InstructionKind::Ret => {
                    assert_eq!(ins.operands.len(), 0);
                    assert_eq!(self.stack_offset() % 16, -8);
                    self.set_stack_offset(8); // Pop the return address implicitly.
                }
            }
            trace!("eval end: rsp={}", self.stack_offset());
        }

        // Ensure that the stack is properly reset.
        assert_eq!(self.stack_offset() % 16, 0);
    }
}

impl Operand {
    pub(crate) fn from_memory_location(size: &Size, loc: &MemoryLocation) -> Self {
        Self {
            size: *size,
            kind: loc.into(),
        }
    }

    pub(crate) fn is_reg(&self) -> bool {
        matches!(self.kind, OperandKind::Register(_))
    }

    pub(crate) fn is_effective_address(&self) -> bool {
        matches!(self.kind, OperandKind::EffectiveAddress(_))
    }

    pub(crate) fn is_rm(&self) -> bool {
        self.is_reg() || self.is_effective_address()
    }

    pub(crate) fn as_reg(&self) -> Option<Register> {
        match self.kind {
            OperandKind::Register(reg) => Some(reg),
            _ => None,
        }
    }

    pub(crate) fn as_effective_address(&self) -> Option<EffectiveAddress> {
        match self.kind {
            OperandKind::EffectiveAddress(addr) => Some(addr),
            _ => None,
        }
    }
}

impl EffectiveAddress {
    // Avoid accidentally using RIP-relative addressing:
    // > The ModR/M encoding for RIP-relative addressing does not depend on
    // > using a prefix. Specifically, the r/m bit field encoding of 101B (used
    // > to select RIP-relative addressing) is not affected by the REX prefix.
    // > For example, selecting
    // > R13 (REX.B = 1, r/m = 101B) with mod = 00B still results in
    // > RIP-relative addressing. The 4-bit r/m field of REX.B combined with
    // > ModR/M is not fully decoded. In order to address R13 with no
    // > displacement, software must encode R13 + 0 using a 1-byte displacement
    // > of zero.
    fn can_base_be_mistaken_for_rel_addressing(&self) -> bool {
        self.base == Register::R13 || self.base == Register::Rbp
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.kind.to_str())?;
        self.operands.iter().enumerate().try_for_each(|(i, o)| {
            if i == 0 {
                f.write_str(" ")?;
            } else {
                f.write_str(", ")?;
            }

            write!(f, "{}", o)
        })
    }
}

impl From<&MemoryLocation> for OperandKind {
    fn from(value: &MemoryLocation) -> Self {
        match value {
            MemoryLocation::Register(asm::Register::Amd64(reg)) => OperandKind::Register(*reg),
            MemoryLocation::Stack(off) => OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rsp,
                index: None,
                scale: Scale::_0,
                displacement: (*off).try_into().unwrap(), // TODO: handle gracefully,
            }),
        }
    }
}

impl From<MemoryLocation> for OperandKind {
    fn from(value: MemoryLocation) -> Self {
        (&value).into()
    }
}

impl From<OperandKind> for MemoryLocation {
    fn from(value: OperandKind) -> Self {
        (&value).into()
    }
}

impl From<&OperandKind> for MemoryLocation {
    fn from(value: &OperandKind) -> Self {
        match value {
            OperandKind::Register(register) => {
                MemoryLocation::Register(asm::Register::Amd64(*register))
            }
            OperandKind::Immediate(_imm) => panic!(),
            OperandKind::EffectiveAddress(EffectiveAddress {
                base: Register::Rsp,
                displacement,
                ..
            }) => MemoryLocation::Stack(*displacement as isize),
            OperandKind::EffectiveAddress(_) => todo!(),
            OperandKind::FnName(_) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::process::Stdio;

    use proptest::prelude::*;

    use super::*;

    #[test]
    fn test_encoding() {
        {
            let ins = Instruction {
                kind: InstructionKind::Push,
                operands: vec![Operand {
                    kind: OperandKind::Register(Register::R15),
                    size: Size::_64,
                }],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(2);
            ins.encode(&mut w).unwrap();
            assert_eq!(&w, &[0x41, 0x57]);
        }

        {
            let ins = Instruction {
                kind: InstructionKind::Pop,
                operands: vec![Operand {
                    kind: OperandKind::Register(Register::Rbx),
                    size: Size::_64,
                }],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(2);
            ins.encode(&mut w).unwrap();
            assert_eq!(&w, &[0x5b]);
        }

        {
            let ins = Instruction {
                kind: InstructionKind::Lea,
                operands: vec![
                    Operand {
                        kind: OperandKind::Register(Register::R8),
                        size: Size::_64,
                    },
                    Operand {
                        kind: OperandKind::EffectiveAddress(EffectiveAddress {
                            base: Register::R13,
                            index: Some(Register::R14),
                            scale: Scale::_8,
                            displacement: 42,
                        }),
                        size: Size::_64,
                    },
                ],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            ins.encode(&mut w).unwrap();
            assert_eq!(&w, &[0x4f, 0x8d, 0x44, 0xf5, 0x2a]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Push,
                operands: vec![Operand {
                    kind: OperandKind::EffectiveAddress(EffectiveAddress {
                        base: Register::R12,
                        index: Some(Register::Rbx),
                        scale: Scale::_4,
                        displacement: 1,
                    }),
                    size: Size::_64,
                }],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            ins.encode(&mut w).unwrap();
            assert_eq!(&w, &[0x41, 0xff, 0x74, 0x9c, 0x01]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Pop,
                operands: vec![Operand {
                    kind: OperandKind::EffectiveAddress(EffectiveAddress {
                        base: Register::R12,
                        index: Some(Register::Rbx),
                        scale: Scale::_4,
                        displacement: 1,
                    }),
                    size: Size::_64,
                }],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            ins.encode(&mut w).unwrap();
            assert_eq!(&w, &[0x41, 0x8f, 0x44, 0x9c, 0x01]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::IDiv,
                operands: vec![Operand {
                    kind: OperandKind::EffectiveAddress(EffectiveAddress {
                        base: Register::R12,
                        index: Some(Register::Rbx),
                        scale: Scale::_4,
                        displacement: 1,
                    }),
                    size: Size::_64,
                }],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            ins.encode(&mut w).unwrap();
            assert_eq!(&w, &[0x49, 0xf7, 0x7c, 0x9c, 0x01]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Mov,
                operands: vec![
                    Operand {
                        kind: OperandKind::Register(Register::Rbp),
                        size: Size::_64,
                    },
                    Operand {
                        kind: OperandKind::Register(Register::Rsp),
                        size: Size::_64,
                    },
                ],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            ins.encode(&mut w).unwrap();
            assert_eq!(&w, &[0x48, 0x89, 0xe5]);
        }
    }

    fn oracle_encode(ins: &Instruction) -> std::io::Result<Vec<u8>> {
        let mut child = std::process::Command::new("clang")
            .args(&[
                "--target=x86_64-unknown-linux",
                "-static",
                "-fuse-ld=lld",
                "-mllvm",
                "--x86-asm-syntax=intel",
                "-x",
                "assembler",
                "-O0",
                "-nostdlib",
                "-Wl,--oformat=binary",
                "-o",
                "/dev/stdout", // FIXME: Windows.
                "-",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;

        {
            let mut stdin = child.stdin.take().unwrap();
            write!(&mut stdin, "{}", ins)?;
        }
        let output = child.wait_with_output()?;

        Ok(output.stdout)
    }

    #[test]
    fn test_encode_oracle() {
        let ins = Instruction {
            kind: InstructionKind::Mov,
            operands: vec![
                Operand {
                    kind: OperandKind::Register(Register::Rbp),
                    size: Size::_64,
                },
                Operand {
                    kind: OperandKind::Register(Register::Rsp),
                    size: Size::_64,
                },
            ],
            origin: Origin::new_unknown(),
        };
        let mut actual = Vec::with_capacity(5);
        ins.encode(&mut actual).unwrap();

        if let Ok(expected) = oracle_encode(&ins) {
            assert_eq!(actual, expected);
        }
    }

    prop_compose! {
        fn arb_instruction()(
            kind in any::<InstructionKind>(),
            // Generates a Vec of Operand with size between 0 and 2
            operands in prop::collection::vec(any::<Operand>(), 0..=2)
        ) -> Instruction {
            Instruction { kind, operands ,origin:Origin::new_unknown()}
        }
    }

    proptest! {
        #[test]
        fn test_encode_proptest(ins in arb_instruction()){
        let mut actual = Vec::with_capacity(15);

        match (ins.encode(&mut actual), oracle_encode(&ins)) {
            (Ok(()), Ok(expected)) => assert_eq!(actual, expected),
            (Err(_), Err(_)) => {},
            (actual,oracle) => panic!("oracle and implementation do not agree: actual={:#?} oracle={:#?} ins={}",actual,oracle, ins )
        }
        }
    }
}
