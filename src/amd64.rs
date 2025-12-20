use std::{io::Write, panic};

use log::trace;
use serde::Serialize;

use crate::{
    amd64,
    asm::{self, Abi, EvalResult, Operand, OperandKind, Stack},
    ir::{self, EvalValue, EvalValueKind},
    origin::Origin,
    register_alloc::{MemoryLocation, RegisterMapping},
    type_checker::Size,
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

#[derive(Serialize, Debug, Clone, Copy)]
#[allow(non_camel_case_types)]
#[repr(u16)]
pub enum InstructionKind {
    Mov_R_RM,
    Mov_R_Imm,
    Mov_RM_R,
    Mov_RM_Imm,
    Add_R_RM,
    Add_RM_Imm,
    Add_RM_R,
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
                        (InstructionKind::Add_RM_R, rhs_loc)
                    }
                    (MemoryLocation::Register(_), MemoryLocation::Stack(_)) => {
                        (InstructionKind::Add_R_RM, rhs_loc)
                    }
                    (MemoryLocation::Stack(_), MemoryLocation::Register(_)) => {
                        (InstructionKind::Add_RM_R, rhs_loc)
                    }
                    (MemoryLocation::Stack(_), MemoryLocation::Stack(_)) => {
                        self.emit_store(
                            &MemoryLocation::Register(asm::Register::Amd64(Register::R11)),
                            &((*rhs_loc).into()),
                            &Size::_64,
                            &Origin::new_synth_codegen(),
                        );
                        (
                            InstructionKind::Add_RM_R,
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
                    kind: InstructionKind::IMul_R_RM,
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
                kind: OperandKind::Register(asm::Register::Amd64(Register::Rbp)),
            }],
            origin: Origin::new_synth_codegen(),
        });
        self.emit_store(
            &MemoryLocation::Register(asm::Register::Amd64(Register::Rbp)),
            &OperandKind::Register(asm::Register::Amd64(Register::Rsp)),
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
                kind: InstructionKind::Add_RM_Imm,
                operands: vec![
                    Operand {
                        size: Size::_64,
                        kind: OperandKind::Register(asm::Register::Amd64(Register::Rsp)),
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
                kind: InstructionKind::Add_RM_Imm,
                operands: vec![
                    Operand {
                        size: Size::_64,
                        kind: OperandKind::Register(asm::Register::Amd64(Register::Rsp)),
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
                kind: OperandKind::Register(asm::Register::Amd64(Register::Rbp)),
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
            (MemoryLocation::Register(dst_reg), OperandKind::Immediate(src_imm)) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_R_Imm,
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
            (MemoryLocation::Stack(dst_stack), OperandKind::Register(src_reg)) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_RM_R,
                    operands: vec![
                        Operand {
                            size: *size,
                            kind: OperandKind::Stack(*dst_stack),
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
                    kind: InstructionKind::Mov_RM_Imm,
                    operands: vec![
                        Operand {
                            size: *size,
                            kind: OperandKind::Stack(*off),
                        },
                        Operand {
                            size: *size,
                            kind: src.clone(),
                        },
                    ],
                    origin: *origin,
                });
            }
            (MemoryLocation::Register(dst_reg), OperandKind::Stack(_)) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov_R_RM,
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
            (MemoryLocation::Stack(dst), OperandKind::Stack(src)) if dst == src => {
                // noop.
            }
            (MemoryLocation::Stack(_), OperandKind::Stack(_)) => todo!(),
        }
    }
}

impl Register {
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
            Register::Rbp => true,
            Register::Rsp => true,
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
            InstructionKind::Mov_RM_R
            | InstructionKind::Mov_R_RM
            | InstructionKind::Mov_R_Imm
            | InstructionKind::Mov_RM_Imm => "mov",
            InstructionKind::Add_R_RM | InstructionKind::Add_RM_Imm | InstructionKind::Add_RM_R => {
                "add"
            }
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

    pub(crate) fn encode(&self, ins: &Instruction) -> Vec<u8> {
        match self {
            InstructionKind::Mov_R_RM => todo!(),
            InstructionKind::Mov_R_Imm => todo!(),
            InstructionKind::Mov_RM_R => todo!(),
            InstructionKind::Mov_RM_Imm => todo!(),
            InstructionKind::Add_R_RM => todo!(),
            InstructionKind::Add_RM_Imm => todo!(),
            InstructionKind::Add_RM_R => todo!(),
            InstructionKind::IMul_R_RM => todo!(),
            InstructionKind::IDiv => todo!(),
            InstructionKind::Lea => todo!(),
            InstructionKind::Call => {
                let displacement: i32 = 0; // FIXME: resolve offset with linker.
                let mut res = vec![0xe8]; // Call near.
                res.extend(displacement.to_le_bytes());
                res
            }
            InstructionKind::Push => {
                assert_eq!(ins.operands.len(), 1);

                let op = ins.operands.first().unwrap();
                match op.kind {
                    OperandKind::Register(_) => todo!(),
                    OperandKind::Stack(_) => todo!(),
                    _ => panic!("invalid argument"),
                }
            }
            InstructionKind::Pop => {
                assert_eq!(ins.operands.len(), 1);

                let op = ins.operands.first().unwrap();
                match op.kind {
                    OperandKind::Register(_) => todo!(),
                    OperandKind::Stack(_) => todo!(),
                    _ => panic!("invalid argument"),
                }
            }
            InstructionKind::Ret => vec![0xC3], // Near return.
        }
    }
}

impl Instruction {
    // > A REX prefix is necessary only if an instruction references
    // > one of the extended registers or one of the byte registers SPL, BPL, SIL,
    // DIL;
    // > or uses a 64-bit operand.
    fn is_rex_needed(operands: &[Operand]) -> bool {
        for op in operands {
            if let OperandKind::Register(asm::Register::Amd64(reg)) = op.kind
                && reg.is_extended()
            {
                return true;
            }

            if let OperandKind::Register(asm::Register::Amd64(reg)) = op.kind
                && op.size == Size::_8
                && (reg == Register::Rsp
                    || reg == Register::Rbp
                    || reg == Register::Rsi
                    || reg == Register::Rdi)
            {
                return true;
            }

            if op.size == Size::_64 {
                return true;
            }
        }
        false
    }

    fn encode_rex(
        is_64_bit_operand_size: bool,
        modrm_reg_extended: bool,
        sib_extended: bool,
        modrm_rm_or_sib_or_opcode_reg_extended: bool,
        operands: &[Operand],
    ) -> Option<u8> {
        if !Self::is_rex_needed(operands) {
            return None;
        }

        let mut res = 0b0100_0000;

        if is_64_bit_operand_size {
            // W
            res |= 0b0000_1000;
        }

        if modrm_reg_extended {
            // R
            res |= 0b0000_0100;
        }

        if sib_extended {
            // X
            res |= 0b0000_0010;
        }

        if modrm_rm_or_sib_or_opcode_reg_extended {
            // B
            res |= 0b0000_0001;
        }

        Some(res)
    }

    // Format: `mod (2 bits) | reg (3 bits) | rm (3bits)`.
    fn encode_modrm(encoding: ModRmEncoding, op_rm: &Operand, op_reg: &Operand) -> u8 {
        let reg: u8 = match encoding {
            ModRmEncoding::Slash0 => 0,
            ModRmEncoding::Slash1 => 1,
            ModRmEncoding::Slash2 => 2,
            ModRmEncoding::Slash3 => 3,
            ModRmEncoding::Slash4 => 4,
            ModRmEncoding::Slash5 => 5,
            ModRmEncoding::Slash6 => 6,
            ModRmEncoding::Slash7 => 7,
            ModRmEncoding::SlashR => todo!(),
        };
        assert!(reg <= 0b111); // Fits in 3 bits.

        let (mod_, rm): (u8, u8) = match op_rm.kind {
            OperandKind::Register(_) => (0b11, todo!()),
            OperandKind::Immediate(imm) => (0b00, 0b101),
            OperandKind::Stack(0) => todo!(),
            OperandKind::Stack(off) if off < u8::MAX as isize => todo!(),
            OperandKind::Stack(off) => (0b10, todo!()),
            OperandKind::FnName(_) => todo!(),
        };

        assert!(mod_ <= 0b11); // Fits in 2 bits.
        assert!(rm <= 0b111); // Fits in 3 bits.

        mod_ << 6 | reg << 3 | rm
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut res = Vec::new();

        if let Some(Operand {
            size: Size::_16, ..
        }) = self.operands.first()
        {
            res.push(0x66) // 16 bits prefix.
        }

        res.extend(self.kind.encode(self));
        res
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
            | (OperandKind::Stack(_), OperandKind::Register(_))
            | (OperandKind::Register(_), OperandKind::Stack(_)) => {
                let value = self
                    .state
                    .get(&(&src.kind).into())
                    .unwrap_or(&EvalValue::new_int(0))
                    .clone();
                self.state.insert((&dst.kind).into(), value);
            }
            (OperandKind::Register(_), OperandKind::Immediate(imm))
            | (OperandKind::Stack(_), OperandKind::Immediate(imm)) => {
                self.state
                    .insert((&dst.kind).into(), EvalValue::new_int(*imm));
            }
            (OperandKind::Immediate(_), _) => panic!("invalid store destination"),
            (OperandKind::Stack(_), OperandKind::Stack(_)) => panic!("unsupported store"),
        };
    }

    fn load(&mut self, dst: &Operand, src: &Operand) {
        assert_eq!(dst.size, src.size);

        match (&dst.kind, &src.kind) {
            (OperandKind::Register(_), OperandKind::Stack(_)) => {
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

            let asm::InstructionKind::Amd64(kind) = ins.kind;

            match kind {
                InstructionKind::Mov_R_Imm
                | InstructionKind::Mov_R_RM
                | InstructionKind::Mov_RM_R
                | InstructionKind::Mov_RM_Imm => {
                    assert_eq!(ins.operands.len(), 2);
                    self.store(&ins.operands[0], &ins.operands[1]);
                }
                InstructionKind::Add_R_RM => {
                    assert_eq!(ins.operands.len(), 2);
                    let size = ins.operands[0].size;
                    assert_eq!(size, ins.operands[1].size);

                    assert!(ins.operands[0].is_reg());
                    let dst: MemoryLocation = (&ins.operands[0].kind).into();

                    assert!(ins.operands[1].is_rm());
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
                InstructionKind::Add_RM_R => {
                    assert_eq!(ins.operands.len(), 2);
                    let size = ins.operands[0].size;
                    assert_eq!(size, ins.operands[1].size);

                    assert!(ins.operands[0].is_rm());
                    let dst: MemoryLocation = (&ins.operands[0].kind).into();

                    assert!(ins.operands[1].is_reg());
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
                InstructionKind::Add_RM_Imm => {
                    assert_eq!(ins.operands.len(), 2);
                    let size = ins.operands[0].size;
                    assert_eq!(size, ins.operands[1].size);

                    assert!(ins.operands[0].is_rm());
                    let dst: MemoryLocation = (&ins.operands[0].kind).into();

                    assert!(ins.operands[1].is_imm());
                    if !ins.operands[1].is_imm32() {
                        todo!();
                    }
                    let src = ins.operands[1].as_imm();
                    assert!(src <= i32::MAX as i64);

                    self.state
                        .entry(dst)
                        .and_modify(|e| {
                            *e = EvalValue::new_int(src + e.as_num());
                        })
                        .or_insert(EvalValue::new_int(0));
                }
                InstructionKind::IMul_R_RM => {
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
                        asm::OperandKind::Register(op) => {
                            let op_value = self
                                .state
                                .get(&MemoryLocation::Register(op))
                                .unwrap_or(&EvalValue::new_int(0))
                                .clone();

                            self.state
                                .entry(MemoryLocation::Register(*dst_reg))
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
                    match op.kind {
                        OperandKind::Register(_) | OperandKind::Stack(_) => {}
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
