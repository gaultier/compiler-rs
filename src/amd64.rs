use std::{
    collections::BTreeMap,
    fmt::Display,
    io::{self, Write},
    ops::Neg,
    panic,
};

use log::{error, trace};

#[cfg(test)]
use proptest::proptest;
#[cfg(test)]
use proptest_derive::Arbitrary;

use serde::Serialize;

use crate::{
    asm::{self, Abi, Encoding, Stack, Symbol},
    ir::{self},
    origin::Origin,
    register_alloc::{MemoryLocation, RegisterMapping},
    type_checker::Size,
};

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum Scale {
    _1 = 1,
    _2 = 2,
    _4 = 4,
    _8 = 8,
}

#[derive(Serialize, Debug, Clone, Copy)]
#[cfg_attr(test, derive(Arbitrary))]
pub struct EffectiveAddress {
    base: Option<Register>,
    index_scale: Option<(Register, Scale)>,
    displacement: i32,
    size_override: Option<Size>,
}

#[derive(Serialize, Debug, Clone)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum Operand {
    Register(Register),
    Immediate(i64),
    EffectiveAddress(EffectiveAddress),
    // For now.
    #[cfg_attr(test, proptest(skip))]
    FnName(String),
}

#[derive(Serialize, Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub operands: Vec<Operand>,
    pub origin: Origin,
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(test, derive(Arbitrary))]
#[repr(u8)]
pub enum Register {
    Al,
    Ah,
    Ax,
    Eax,
    Rax,

    Bl,
    Bh,
    Bx,
    Ebx,
    Rbx,

    Cl,
    Ch,
    Cx,
    Ecx,
    Rcx,

    Dl,
    Dh,
    Dx,
    Edx,
    Rdx,

    Dil,
    Di,
    Edi,
    Rdi,

    Sil,
    Si,
    Esi,
    Rsi,

    Bpl,
    Bp,
    Ebp,
    Rbp,

    Spl,
    Sp,
    Esp,
    Rsp,

    R8b,
    R8w,
    R8d,
    R8,

    R9b,
    R9w,
    R9d,
    R9,

    R10b,
    R10w,
    R10d,
    R10,

    R11b,
    R11w,
    R11d,
    R11,

    R12b,
    R12w,
    R12d,
    R12,

    R13b,
    R13w,
    R13d,
    R13,

    R14b,
    R14w,
    R14d,
    R14,

    R15b,
    R15w,
    R15d,
    R15,
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

impl EffectiveAddress {
    fn is_valid(&self) -> bool {
        match self {
            EffectiveAddress {
                index_scale: Some((reg, _)),
                ..
            } if reg.size() < Size::_32 || *reg == Register::Rsp => false,

            EffectiveAddress {
                base: Some(reg), ..
            } if reg.size() < Size::_32 => false,

            // At least base or index must be present.
            EffectiveAddress {
                base: None,
                index_scale: None,
                ..
            } => false,

            // Size of base and index must match.
            EffectiveAddress {
                base: Some(base),
                index_scale: Some((index, _)),
                ..
            } if base.size() != index.size() => false,

            _ => true,
        }
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Operand::Register(reg) => reg.fmt(f),
            Operand::Immediate(n) => write!(f, "{}", n),
            Operand::FnName(name) => f.write_str(name),
            Operand::EffectiveAddress(EffectiveAddress {
                base,
                index_scale,
                displacement,
                size_override,
            }) => {
                if let Some(size) = size_override {
                    write!(f, "{} ", size)?;
                    f.write_str(" ")?;
                }

                f.write_str("[")?;

                if let Some(base) = base {
                    write!(f, "{}", base)?;
                }

                if base.is_some() && index_scale.is_some() {
                    f.write_str(" + ")?;
                }

                if let Some((index, scale)) = index_scale {
                    write!(f, "{}", index)?;
                    if *scale > Scale::_1 {
                        write!(f, "  * {}", *scale as u8)?;
                    }
                }

                if *displacement != 0 {
                    write!(f, " {:+}", displacement)?;
                }

                write!(f, "]")
            }
        }
    }
}

pub(crate) fn encode(instructions: &[asm::Instruction]) -> Encoding {
    let mut w = Vec::with_capacity(instructions.len() * 5);
    let mut symbols = BTreeMap::new();

    symbols.insert(
        String::from("builtin.println_u64"),
        Symbol {
            location: w.len(),
            visibility: asm::Visibility::Local,
            origin: Origin::new_builtin(),
        },
    );

    w.extend_from_slice(&[
        0x55, // push rbp
        0x48, 0x89, 0xe5, // mov rbp, rsp,
        0x48, 0x81, 0xec, 0x00, 0x01, 0x00, 0x00, // sub rsp, 0x100
        0x4c, 0x8d, 0x8d, 0x01, 0xff, 0xff, 0xff, // lea r9, [rbp-0xff]
        0x41, 0xb8, 0x01, 0x00, 0x00, 0x00, // mov r8d, 1
        0x41, 0xc6, 0x01, 0x0a, // mov BYTE PTR [r9], 0x0a ; '\n'
        0x48, 0x89, 0xf8, // mov rax, rdi
    ]);

    symbols.insert(
        String::from("builtin.println_u64.loop"),
        Symbol {
            location: w.len(),
            visibility: asm::Visibility::Local,
            origin: Origin::new_builtin(),
        },
    );
    w.extend_from_slice(&[
        // .loop:
        0x48, 0x83, 0xf8, 0x00, // cmp rax, 0x00
        0x74, 0x1a, // je 3f
        0xb9, 0x0a, 0x00, 0x00, 0x00, // mov ecx, 0xa
        0x48, 0x31, 0xd2, // xor rdx, rdx
        0x48, 0xf7, 0xf1, // div rcx
        0x48, 0x83, 0xc2, 0x30, // add rdx, 0x30
        0x49, 0xff, 0xc9, // dec r9
        0x41, 0x88, 0x11, // mov BYTE PTR [r9], dl
        0x49, 0xff, 0xc0, // inc r8
        0xeb, 0xe0, // jmp r8
    ]);

    symbols.insert(
        String::from("builtin.println_u64.end"),
        Symbol {
            location: w.len(),
            visibility: asm::Visibility::Local,
            origin: Origin::new_builtin(),
        },
    );
    w.extend_from_slice(&[
        // .end:
        0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax, 0x1; SYSCALL_WRITE_LINUX
        0xbf, 0x01, 0x00, 0x00, 0x00, // mov edi, 1; STDOUT
        0x4c, 0x89, 0xce, // mov rsi, r9
        0x4c, 0x89, 0xc2, // mov rdx, r8
        0x0f, 0x05, // syscall
        0xb8, 0x00, 0x00, 0x00, 0x00, // mov eax, 0
        0x48, 0x81, 0xc4, 0x00, 0x01, 0x00, 0x00, // add rsp, 0x100
        0x5d, // pop rbp
        0xc3, // ret
    ]);

    // main
    symbols.insert(
        String::from("main"),
        Symbol {
            location: w.len(),
            visibility: asm::Visibility::Local,
            origin: Origin::new_builtin(),
        },
    );
    for ins in instructions {
        let asm::Instruction::Amd64(ins) = ins;
        ins.encode(&mut w, &symbols).unwrap();
    }

    // Entrypoint.
    let entrypoint = w.len();
    symbols.insert(
        String::from("_start"),
        Symbol {
            location: w.len(),
            visibility: asm::Visibility::Global,
            origin: Origin::new_builtin(),
        },
    );
    {
        let ins_call = Instruction {
            kind: InstructionKind::Call,
            operands: vec![Operand::FnName(String::from("main"))],
            origin: Origin::new_unknown(),
        };
        ins_call.encode(&mut w, &symbols).unwrap();
    }

    // Exit.
    {
        let ins_mov = Instruction {
            kind: InstructionKind::Mov,
            operands: vec![Operand::Register(Register::Eax), Operand::Immediate(60)], //FIXME
            origin: Origin::new_unknown(),
        };
        ins_mov.encode(&mut w, &symbols).unwrap();
    }
    {
        let ins_mov = Instruction {
            kind: InstructionKind::Mov,
            operands: vec![Operand::Register(Register::Edi), Operand::Immediate(0)],
            origin: Origin::new_unknown(),
        };
        ins_mov.encode(&mut w, &symbols).unwrap();
    }
    {
        let ins_syscall = Instruction {
            kind: InstructionKind::Syscall,
            operands: vec![],
            origin: Origin::new_unknown(),
        };
        ins_syscall.encode(&mut w, &symbols).unwrap();
    }

    Encoding {
        instructions: w,
        entrypoint,
        symbols,
    }
}

impl Scale {
    fn to_2_bits(self) -> u8 {
        match self {
            Scale::_1 => 0b00,
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

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Arbitrary))]
#[allow(non_camel_case_types)]
#[repr(u16)]
pub enum InstructionKind {
    Mov,
    Add,
    IMul,
    IDiv,
    Lea,
    // For now. Need basic linker to compute the relative displacement.
    #[cfg_attr(test, proptest(skip))]
    Call,
    Push,
    Pop,
    Ret,
    Syscall,
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
                        vreg_to_memory_location
                            .get(&ins.res_vreg.unwrap())
                            .unwrap()
                            .into(),
                        rhs_loc.into(),
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
                    &ins.origin,
                );
                self.asm.push(Instruction {
                    kind: InstructionKind::IMul,
                    operands: vec![
                        vreg_to_memory_location
                            .get(&ins.res_vreg.unwrap())
                            .unwrap()
                            .into(),
                        vreg_to_memory_location.get(rhs).unwrap().into(),
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
                        &Origin::new_synth_codegen(),
                    );
                    trace!("spill rax before idiv: spill_slot={:#?}", spill_slot);

                    spill_slot
                };

                let lhs = vreg_to_memory_location.get(lhs).unwrap();
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)),
                    &lhs.into(),
                    &Origin::new_synth_codegen(),
                );

                // `idiv` technically divides the 128 bit `rdx:rax` value. Thus, `rdx` is zeroed
                // first to only divide `rax`.
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                    &Operand::Immediate(0),
                    &ins.origin,
                );
                self.asm.push(Instruction {
                    kind: InstructionKind::IDiv,
                    operands: vec![vreg_to_memory_location.get(rhs).unwrap().into()],
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
                        &ins.origin,
                    );
                }

                // Finally: restore rax & rdx.
                {
                    trace!("unspill rdx after idiv: spill_slot={:#?}", &rdx_spill_slot);
                    self.emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rdx)),
                        &rdx_spill_slot.into(),
                        &Origin::new_synth_codegen(),
                    );

                    trace!("unspill rax after idiv: spill_slot={:#?}", rax_spill_slot);
                    self.emit_store(
                        &MemoryLocation::Register(asm::Register::Amd64(Register::Rax)),
                        &rax_spill_slot.into(),
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
                    &Operand::Immediate(*num),
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
                    &Operand::Immediate(if *b { 1 } else { 0 }),
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
            ) if fn_name == "builtin.println_u64" => {
                let arg: Operand = vreg_to_memory_location.get(vreg).unwrap().into();

                let spill_slot = self.find_free_spill_slot(&Size::_64);
                self.emit_store(
                    &spill_slot,
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)).into(),
                    &Origin::new_synth_codegen(),
                );
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)),
                    &arg,
                    &Origin::new_synth_codegen(),
                );

                self.asm.push(Instruction {
                    kind: InstructionKind::Call,
                    operands: vec![Operand::FnName(fn_name.clone())],
                    origin: ins.origin,
                });
                self.emit_store(
                    &MemoryLocation::Register(asm::Register::Amd64(Register::Rdi)),
                    &spill_slot.into(),
                    &Origin::new_synth_codegen(),
                );
            }
            x => panic!("invalid IR operands: {:#?}", x),
        }
    }

    pub(crate) fn emit_fn_def(
        &mut self,
        fn_def: &ir::FnDef,
        vreg_to_memory_location: &RegisterMapping,
    ) {
        self.asm = Vec::with_capacity(fn_def.instructions.len() * 2);

        self.asm.push(Instruction {
            kind: InstructionKind::Push,
            operands: vec![Operand::Register(Register::Rbp)],
            origin: Origin::new_synth_codegen(),
        });
        self.emit_store(
            &MemoryLocation::Register(asm::Register::Amd64(Register::Rbp)),
            &Operand::Register(Register::Rsp),
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
                    Operand::Register(Register::Rsp),
                    Operand::Immediate(stack_offset_frame),
                ],
                origin: Origin::new_synth_codegen(),
            });
        }

        for ir in &fn_def.instructions {
            self.instruction_selection(ir, vreg_to_memory_location);
        }

        // Restore stack.
        if stack_offset_frame != 0 {
            self.asm.push(Instruction {
                kind: InstructionKind::Add,
                operands: vec![
                    Operand::Register(Register::Rsp),
                    Operand::Immediate(-(stack_offset_frame)),
                ],
                origin: Origin::new_synth_codegen(),
            });
        }
        self.asm.push(Instruction {
            kind: InstructionKind::Pop,
            operands: vec![Operand::Register(Register::Rbp)],
            origin: Origin::new_synth_codegen(),
        });

        // Ret
        self.asm.push(Instruction {
            kind: InstructionKind::Ret,
            operands: vec![],
            origin: Origin::new_synth_codegen(),
        });
    }

    pub(crate) fn emit_store(&mut self, dst: &MemoryLocation, src: &Operand, origin: &Origin) {
        match (dst, src) {
            (_, Operand::FnName(_)) => {
                todo!()
            }
            (
                MemoryLocation::Register(asm::Register::Amd64(dst_reg)),
                Operand::Register(src_reg),
            ) if dst_reg == src_reg => {
                // noop.
            }
            (
                MemoryLocation::Register(asm::Register::Amd64(dst_reg)),
                Operand::Register(src_reg),
            ) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![Operand::Register(*dst_reg), Operand::Register(*src_reg)],
                    origin: *origin,
                });
            }
            (
                MemoryLocation::Register(asm::Register::Amd64(dst_reg)),
                Operand::Immediate(src_imm),
            ) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![Operand::Register(*dst_reg), Operand::Immediate(*src_imm)],
                    origin: *origin,
                });
            }
            (MemoryLocation::Stack(_), Operand::Register(src_reg)) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![dst.into(), Operand::Register(*src_reg)],
                    origin: *origin,
                });
            }
            (MemoryLocation::Stack(off), Operand::Immediate(imm)) => {
                if !((i32::MIN as i64)..=(i32::MAX as i64)).contains(imm) {
                    todo!();
                }

                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![
                        Operand::EffectiveAddress(EffectiveAddress {
                            base: Some(Register::Rsp),
                            index_scale: None,
                            displacement: (*off).try_into().unwrap(),
                            size_override: None, // TODO: Revisit,
                        }),
                        src.clone(),
                    ],
                    origin: *origin,
                });
            }
            (
                MemoryLocation::Register(asm::Register::Amd64(dst_reg)),
                Operand::EffectiveAddress(_),
            ) => {
                self.asm.push(Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![Operand::Register(*dst_reg), src.clone()],
                    origin: *origin,
                });
            }
            (
                MemoryLocation::Stack(dst),
                Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(Register::Rsp),
                    index_scale: None,
                    displacement,
                    size_override: None, // TODO: Revisit,
                }),
            ) if *dst == (*displacement as isize) => {
                // noop.
            }
            (MemoryLocation::Stack(_), Operand::EffectiveAddress(_)) => todo!(),
        }
    }
}

impl Register {
    fn is_64_bits(&self) -> bool {
        matches!(
            self,
            Register::Rax
                | Register::Rbx
                | Register::Rcx
                | Register::Rdx
                | Register::Rdi
                | Register::Rsi
                | Register::Rbp
                | Register::Rsp
                | Register::R8
                | Register::R9
                | Register::R10
                | Register::R11
                | Register::R12
                | Register::R13
                | Register::R14
                | Register::R15
        )
    }

    fn is_32_bits(&self) -> bool {
        matches!(
            self,
            Register::Eax
                | Register::Ebx
                | Register::Ecx
                | Register::Edx
                | Register::Edi
                | Register::Esi
                | Register::Ebp
                | Register::Esp
                | Register::R8d
                | Register::R9d
                | Register::R10d
                | Register::R11d
                | Register::R12d
                | Register::R13d
                | Register::R14d
                | Register::R15d
        )
    }

    fn is_16_bits(&self) -> bool {
        matches!(
            self,
            Register::Ax
                | Register::Bx
                | Register::Cx
                | Register::Dx
                | Register::Di
                | Register::Si
                | Register::Bp
                | Register::Sp
                | Register::R8w
                | Register::R9w
                | Register::R10w
                | Register::R11w
                | Register::R12w
                | Register::R13w
                | Register::R14w
                | Register::R15w
        )
    }

    fn is_8_bits(&self) -> bool {
        matches!(
            self,
            Register::Ah
                | Register::Al
                | Register::Bh
                | Register::Bl
                | Register::Ch
                | Register::Cl
                | Register::Dh
                | Register::Dl
                | Register::Dil
                | Register::Sil
                | Register::Bpl
                | Register::Spl
                | Register::R8b
                | Register::R9b
                | Register::R10b
                | Register::R11b
                | Register::R12b
                | Register::R13b
                | Register::R14b
                | Register::R15b
        )
    }

    fn size(&self) -> Size {
        match self {
            Register::Rax
            | Register::Rbx
            | Register::Rcx
            | Register::Rdx
            | Register::Rdi
            | Register::Rsi
            | Register::Rbp
            | Register::Rsp
            | Register::R8
            | Register::R9
            | Register::R10
            | Register::R11
            | Register::R12
            | Register::R13
            | Register::R14
            | Register::R15 => Size::_64,

            Register::Eax
            | Register::Ebx
            | Register::Ecx
            | Register::Edx
            | Register::Edi
            | Register::Esi
            | Register::Ebp
            | Register::Esp
            | Register::R8d
            | Register::R9d
            | Register::R10d
            | Register::R11d
            | Register::R12d
            | Register::R13d
            | Register::R14d
            | Register::R15d => Size::_32,

            Register::Ax
            | Register::Bx
            | Register::Cx
            | Register::Dx
            | Register::Di
            | Register::Si
            | Register::Bp
            | Register::Sp
            | Register::R8w
            | Register::R9w
            | Register::R10w
            | Register::R11w
            | Register::R12w
            | Register::R13w
            | Register::R14w
            | Register::R15w => Size::_16,

            Register::Ah
            | Register::Al
            | Register::Bh
            | Register::Bl
            | Register::Ch
            | Register::Cl
            | Register::Dh
            | Register::Dl
            | Register::Dil
            | Register::Sil
            | Register::Bpl
            | Register::Spl
            | Register::R8b
            | Register::R9b
            | Register::R10b
            | Register::R11b
            | Register::R12b
            | Register::R13b
            | Register::R14b
            | Register::R15b => Size::_8,
        }
    }

    // TODO: Use.
    fn is_high_byte(&self) -> bool {
        matches!(
            self,
            Register::Ah | Register::Ch | Register::Dh | Register::Bh
        )
    }

    fn to_3_bits(self) -> u8 {
        let res = match self {
            Register::Al | Register::Ax | Register::Eax | Register::Rax => 0b000,
            Register::Bl | Register::Bx | Register::Ebx | Register::Rbx => 0b011,
            Register::Cl | Register::Cx | Register::Ecx | Register::Rcx => 0b001,
            Register::Dl | Register::Dx | Register::Edx | Register::Rdx => 0b010,
            Register::Bh | Register::Dil | Register::Di | Register::Edi | Register::Rdi => 0b111,
            Register::Dh | Register::Si | Register::Sil | Register::Esi | Register::Rsi => 0b110,
            Register::Ch | Register::Bpl | Register::Bp | Register::Ebp | Register::Rbp => 0b101,
            Register::Ah | Register::Spl | Register::Sp | Register::Esp | Register::Rsp => 0b100,
            Register::R8b | Register::R8w | Register::R8d | Register::R8 => 0b000,
            Register::R9b | Register::R9w | Register::R9d | Register::R9 => 0b001,
            Register::R10b | Register::R10w | Register::R10d | Register::R10 => 0b010,
            Register::R11b | Register::R11w | Register::R11d | Register::R11 => 0b011,
            Register::R12b | Register::R12w | Register::R12d | Register::R12 => 0b100,
            Register::R13b | Register::R13w | Register::R13d | Register::R13 => 0b101,
            Register::R14b | Register::R14w | Register::R14d | Register::R14 => 0b110,
            Register::R15b | Register::R15w | Register::R15d | Register::R15 => 0b111,
        };
        assert!(res <= 0b111);
        res
    }

    pub fn is_extended(&self) -> bool {
        matches!(
            self,
            Register::R8b
                | Register::R8w
                | Register::R8d
                | Register::R8
                | Register::R9b
                | Register::R9w
                | Register::R9d
                | Register::R9
                | Register::R10b
                | Register::R10w
                | Register::R10d
                | Register::R10
                | Register::R11b
                | Register::R11w
                | Register::R11d
                | Register::R11
                | Register::R12b
                | Register::R12w
                | Register::R12d
                | Register::R12
                | Register::R13b
                | Register::R13w
                | Register::R13d
                | Register::R13
                | Register::R14b
                | Register::R14w
                | Register::R14d
                | Register::R14
                | Register::R15b
                | Register::R15w
                | Register::R15d
                | Register::R15
        )
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Register::Al => f.write_str("al"),
            Register::Ah => f.write_str("ah"),
            Register::Ax => f.write_str("ax"),
            Register::Eax => f.write_str("eax"),
            Register::Rax => f.write_str("rax"),

            Register::Bl => f.write_str("bl"),
            Register::Bh => f.write_str("bh"),
            Register::Bx => f.write_str("bx"),
            Register::Ebx => f.write_str("ebx"),
            Register::Rbx => f.write_str("rbx"),

            Register::Cl => f.write_str("cl"),
            Register::Ch => f.write_str("ch"),
            Register::Cx => f.write_str("cx"),
            Register::Ecx => f.write_str("ecx"),
            Register::Rcx => f.write_str("rcx"),

            Register::Dl => f.write_str("dl"),
            Register::Dh => f.write_str("dh"),
            Register::Dx => f.write_str("dx"),
            Register::Edx => f.write_str("edx"),
            Register::Rdx => f.write_str("rdx"),

            Register::Dil => f.write_str("dil"),
            Register::Di => f.write_str("di"),
            Register::Edi => f.write_str("edi"),
            Register::Rdi => f.write_str("rdi"),

            Register::Sil => f.write_str("sil"),
            Register::Si => f.write_str("si"),
            Register::Esi => f.write_str("esi"),
            Register::Rsi => f.write_str("rsi"),

            Register::Bpl => f.write_str("bpl"),
            Register::Bp => f.write_str("bp"),
            Register::Ebp => f.write_str("ebp"),
            Register::Rbp => f.write_str("rbp"),

            Register::Spl => f.write_str("spl"),
            Register::Sp => f.write_str("sp"),
            Register::Esp => f.write_str("esp"),
            Register::Rsp => f.write_str("rsp"),

            Register::R8b => f.write_str("r8b"),
            Register::R8w => f.write_str("r8w"),
            Register::R8d => f.write_str("r8d"),
            Register::R8 => f.write_str("r8"),

            Register::R9b => f.write_str("r9b"),
            Register::R9w => f.write_str("r9w"),
            Register::R9d => f.write_str("r9d"),
            Register::R9 => f.write_str("r9"),

            Register::R10b => f.write_str("r10b"),
            Register::R10w => f.write_str("r10w"),
            Register::R10d => f.write_str("r10d"),
            Register::R10 => f.write_str("r10"),

            Register::R11b => f.write_str("r11b"),
            Register::R11w => f.write_str("r11w"),
            Register::R11d => f.write_str("r11d"),
            Register::R11 => f.write_str("r11"),

            Register::R12b => f.write_str("r12b"),
            Register::R12w => f.write_str("r12w"),
            Register::R12d => f.write_str("r12d"),
            Register::R12 => f.write_str("r12"),

            Register::R13b => f.write_str("r13b"),
            Register::R13w => f.write_str("r13w"),
            Register::R13d => f.write_str("r13d"),
            Register::R13 => f.write_str("r13"),

            Register::R14b => f.write_str("r14b"),
            Register::R14w => f.write_str("r14w"),
            Register::R14d => f.write_str("r14d"),
            Register::R14 => f.write_str("r14"),

            Register::R15b => f.write_str("r15b"),
            Register::R15w => f.write_str("r15w"),
            Register::R15d => f.write_str("r15d"),
            Register::R15 => f.write_str("r15"),
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
            InstructionKind::Syscall => "syscall",
        }
    }
}

impl Instruction {
    // w: register is extended (r8-r15) OR manipulates operand size
    // r: modr/m reg field is extended
    // x: the index field in SIB is extended
    // b: modr/m r/m OR the base field in SIB OR the opcode reg field used for accessing GPRs is extended
    fn encode_rex<W: Write>(
        wr: &mut W,
        w: bool,
        r: bool,
        x: bool,
        b: bool,
        operands: &[&Operand],
    ) -> std::io::Result<()> {
        let mut required = w | r | x | b;
        // > A REX prefix is necessary only if an instruction references
        // > one of the extended registers or one of the byte registers SPL, BPL, SIL,
        // DIL;
        // > or uses a 64-bit operand.
        for op in operands {
            match op {
                Operand::Register(
                    Register::Spl | Register::Bpl | Register::Sil | Register::Dil,
                )
                | Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(Register::Spl | Register::Bpl | Register::Sil | Register::Dil),
                    ..
                })
                | Operand::EffectiveAddress(EffectiveAddress {
                    index_scale:
                        Some((Register::Spl | Register::Bpl | Register::Sil | Register::Dil, _)),
                    ..
                }) => {
                    required = true;
                    break;
                }

                Operand::Register(reg)
                | Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(reg), ..
                })
                | Operand::EffectiveAddress(EffectiveAddress {
                    index_scale: Some((reg, _)),
                    ..
                }) if reg.is_extended() => {
                    required = true;
                    break;
                }

                _ => {}
            }
        }
        if !required {
            return Ok(());
        }

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

        wr.write_all(&[res])
    }

    fn encode_rex_from_operands<W: Write>(
        w: &mut W,
        wide: bool,
        op_modrm_rm: Option<&Operand>,
        op_modrm_reg: Option<&Operand>,
        op_reg: Option<&Operand>,
    ) -> std::io::Result<()> {
        // > The REX.R bit adds a 1-bit extension (in the most significant bit position)
        // > to the ModRM.reg field when that field encodes a GPR, YMM/XMM, control,
        // > or debug register. REX.R does not modify ModRM.reg
        // > when that field specifies other registers or is used to extend the opcode.
        // > REX.R is ignored in such cases.
        let r = matches!( op_modrm_reg ,
            Some(Operand::Register(reg)) if reg.is_extended() );

        // > The REX.X bit adds a 1-bit (msb) extension to the SIB.index field.
        let x = match op_modrm_rm {
            Some(Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((_, Scale::_1)),
                ..
            })) => false, // Treat as: [base].
            Some(Operand::EffectiveAddress(EffectiveAddress {
                index_scale: Some((reg, _)),
                ..
            })) if reg.is_extended() => true,
            _ => false,
        };

        // > The REX.B bit adds a 1-bit (msb) extension to either the
        // > ModRM.r/m field to specify a GPR or XMM register,
        // > or to the SIB.base field to specify a GPR.
        let mut b = match op_modrm_rm {
            Some(Operand::Register(reg)) if reg.is_extended() => true,
            Some(Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg), ..
            }))
            | Some(Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                ..
            })) if reg.is_extended() => true,
            _ => false,
        };

        // Or, the register is embedded in the opcode, in which case,
        // REX.B is set when this register is extended.
        b |= matches!(op_reg ,
            Some(Operand::Register(reg)) if reg.is_extended() );

        let ops: Vec<&Operand> = [op_modrm_rm, op_modrm_reg, op_reg]
            .into_iter()
            .flatten()
            .collect();

        Instruction::encode_rex(w, wide, r, x, b, ops.as_slice())
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

        let (mod_, rm): (u8, u8) = match op_rm {
            Operand::Register(reg) => (0b11, reg.to_3_bits()),
            Operand::Immediate(_) => (0b00, 0b101),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement: 0,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement: 0,
                ..
            }) if reg.to_3_bits() == 0b000 => (0b00, 0b000),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement: 0,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement: 0,
                ..
            }) if reg.to_3_bits() == 0b001 => (0b00, 0b001),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement: 0,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement: 0,
                ..
            }) if reg.to_3_bits() == 0b010 => (0b00, 0b010),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement: 0,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement: 0,
                ..
            }) if reg.to_3_bits() == 0b011 => (0b00, 0b011),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement: 0,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement: 0,
                ..
            }) if reg.to_3_bits() == 0b110 => (0b00, 0b110),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement: 0,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement: 0,
                ..
            }) if reg.to_3_bits() == 0b111 => (0b00, 0b111),
            // TODO: case for disp32
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement,
                ..
            }) if reg.to_3_bits() == 0b000 && i8::try_from(*displacement).is_ok() => (0b01, 0b000),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement,
                ..
            }) if reg.to_3_bits() == 0b001 && i8::try_from(*displacement).is_ok() => (0b01, 0b001),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement,
                ..
            }) if reg.to_3_bits() == 0b010 && i8::try_from(*displacement).is_ok() => (0b01, 0b010),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement,
                ..
            }) if reg.to_3_bits() == 0b011 && i8::try_from(*displacement).is_ok() => (0b01, 0b011),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement,
                ..
            }) if reg.to_3_bits() == 0b101 && i8::try_from(*displacement).is_ok() => (0b01, 0b101),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                displacement,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                displacement,
                ..
            }) if reg.to_3_bits() == 0b110 && i8::try_from(*displacement).is_ok() => (0b01, 0b110),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                ..
            }) if reg.to_3_bits() == 0b000 => (0b10, 0b000),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                ..
            }) if reg.to_3_bits() == 0b001 => (0b10, 0b001),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                ..
            }) if reg.to_3_bits() == 0b010 => (0b10, 0b010),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                ..
            }) if reg.to_3_bits() == 0b011 => (0b10, 0b011),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                ..
            }) if reg.to_3_bits() == 0b101 => (0b10, 0b101),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                ..
            }) if reg.to_3_bits() == 0b110 => (0b10, 0b110),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg),
                index_scale: None,
                ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some((reg, Scale::_1)),
                ..
            }) if reg.to_3_bits() == 0b111 => (0b10, 0b111),

            // Special case of no base, with index+scale.
            Operand::EffectiveAddress(EffectiveAddress {
                base: None,
                index_scale: Some(_),
                ..
            }) => (0b00, 0b100),

            Operand::EffectiveAddress(EffectiveAddress {
                displacement: 0, ..
            }) => (0b00, 0b100),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(_),
                displacement,
                ..
            }) if i8::try_from(*displacement).is_ok() => (0b01, 0b100),
            Operand::EffectiveAddress(_) => (0b10, 0b100),

            Operand::FnName(_) => todo!(),
        };

        assert!(mod_ <= 0b11); // Fits in 2 bits.
        assert!(rm <= 0b111); // Fits in 3 bits.

        mod_ << 6 | reg << 3 | rm
    }

    fn encode_imm<W: Write>(w: &mut W, imm: i64, size: &Size) -> std::io::Result<()> {
        match size {
            Size::_8 => w.write_all(&(imm as u8).to_le_bytes()),
            Size::_16 => w.write_all(&(imm as u16).to_le_bytes()),
            Size::_32 => w.write_all(&(imm as u32).to_le_bytes()),
            Size::_64 => w.write_all(&imm.to_le_bytes()),
        }
    }

    // Encoding: `Scale(2 bits) | Index(3 bits) | Base (3bits)`.
    fn encode_sib<W: Write>(w: &mut W, addr: &EffectiveAddress, modrm: u8) -> std::io::Result<()> {
        let mod_ = modrm >> 6;
        let rm = modrm & 0b111;
        let is_sib_required = matches!((mod_, rm), (0b00, 0b100) | (0b01, 0b100) | (0b10, 0b100));

        if is_sib_required {
            let scale = addr
                .index_scale
                .map(|(_, scale)| scale.to_2_bits())
                .unwrap_or_default()
                << 6;
            let index = addr
                .index_scale
                .map(|(reg, _)| reg.to_3_bits())
                .unwrap_or_else(|| {
                    assert_eq!(scale, 0);
                    // R12 or RSP: they share the same 3 bits representation.
                    assert_eq!(addr.base.unwrap().to_3_bits(), Register::Rsp.to_3_bits());

                    0b100
                })
                << 3;

            let base = addr.base.map(|reg| reg.to_3_bits()).unwrap_or(0b101);
            let sib = scale | index | base;
            w.write_all(&[sib])?;
        } else {
            // If there is no SIB, then it's impossible for both base and index to be present, and
            // for the scale not to be 1.
            assert!(!(addr.base.is_some() && addr.index_scale.is_some()));
            assert_eq!(
                addr.index_scale
                    .map(|(_, scale)| scale)
                    .unwrap_or(Scale::_1),
                Scale::_1
            );
        }

        // Displacement.
        // > If {mod, r/m} = 00100b, the offset portion of the formula is set to 0.
        // > For {mod, r/m} = 01100b and {mod, r/m} =10100b, offset is encoded in
        // > the one- or 4-byte displacement field of the instruction.
        // > Finally, the encoding {mod, r/m} = 00101b specifies an absolute addressing mode.
        // > In this mode, the > address is provided directly in the instruction encoding
        // > using a 4-byte displacement field. In 64-bit > mode this addressing mode is changed to RIP-relative.
        match (mod_, rm) {
            (0b00, 0b100) if addr.base.is_some() => {} // Nothing to encode, displacement is an implicit 0.
            (0b01, _) => {
                w.write_all(&(addr.displacement as u8).to_le_bytes())?;
            }
            (0b10, _) => {
                w.write_all(&(addr.displacement as u32).to_le_bytes())?;
            }
            (0b00, 0b100) if addr.base.is_none() => {
                w.write_all(&(addr.displacement as u32).to_le_bytes())?;
            }
            (0b00, 0b101) => {
                todo!()
            }
            _ => {}
        }
        Ok(())
    }

    pub(crate) fn encode(
        &self,
        w: &mut Vec<u8>,
        symbols: &BTreeMap<String, Symbol>,
    ) -> std::io::Result<()> {
        trace!("amd64: action=encode ins={}", self);

        // Need Address Size Override Prefix?
        if self.operands.iter().any(|op| {
            matches!( op ,
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(reg), ..
            })
            | Operand::EffectiveAddress(EffectiveAddress {
                index_scale: Some((reg, _)),
                ..
            }) if reg.size() == Size::_32 )
        }) {
            w.write_all(&[0x67])?;
        }

        if self.operands.iter().any(|op| op.size() == Size::_16)
            && self.kind != InstructionKind::Ret
        {
            w.write_all(&[0x66])?; // 16 bits prefix.
        }

        // Reject malformed effective addresses (if any).
        for op in &self.operands {
            if let Some(addr) = op.as_effective_address()
                && !addr.is_valid()
            {
                error!(
                    "amd64: action=encode msg='effective address not valid' addr={:?}",
                    addr
                );
                return Err(std::io::Error::from(io::ErrorKind::InvalidData));
            }
        }

        match self.kind {
            InstructionKind::Mov => {
                if self.operands.len() != 2 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let lhs = &self.operands[0];
                let rhs = &self.operands[1];

                match (lhs, rhs) {
                    // mov r, imm
                    // Encoding: OI 	opcode + rd (w) 	imm8/16/32/64
                    (Operand::Register(reg), Operand::Immediate(imm)) if reg.is_8_bits() => {
                        Instruction::encode_rex_from_operands(w, false, None, None, Some(lhs))?;
                        w.write_all(&[0xB0 | reg.to_3_bits()])?;
                        Instruction::encode_imm(w, *imm, &Size::_8)?;
                    }
                    // MOV r16, imm16
                    (Operand::Register(reg), Operand::Immediate(imm)) if reg.is_16_bits() => {
                        Instruction::encode_rex_from_operands(w, false, None, None, Some(lhs))?;
                        w.write_all(&[0xB8 | reg.to_3_bits()])?;
                        Instruction::encode_imm(w, *imm, &Size::_16)?;
                    }
                    // MOV r32, imm32
                    (Operand::Register(reg), Operand::Immediate(imm)) if reg.is_32_bits() => {
                        Instruction::encode_rex_from_operands(w, false, None, None, Some(lhs))?;
                        w.write_all(&[0xB8 | reg.to_3_bits()])?;
                        Instruction::encode_imm(w, *imm, &Size::_32)?;
                    }
                    // MOV r64, imm64
                    (Operand::Register(reg), Operand::Immediate(imm))
                        if reg.is_64_bits() && *imm > u32::MAX as i64 =>
                    {
                        Instruction::encode_rex_from_operands(w, true, None, None, Some(lhs))?;
                        w.write_all(&[0xB8 | reg.to_3_bits()])?;
                        Instruction::encode_imm(w, *imm, &Size::_64)?;
                    }
                    // mov rm, r
                    // Encoding: MR 	ModRM:r/m (w) 	ModRM:reg (r)
                    (_, Operand::Register(reg))
                        if lhs.is_rm() && reg.is_8_bits() && lhs.size() == rhs.size() =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            false,
                            Some(lhs),
                            Some(rhs),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x88, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (_, Operand::Register(reg))
                        if lhs.is_rm()
                            && (reg.is_16_bits() || reg.is_32_bits())
                            && lhs.size() == rhs.size() =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            false,
                            Some(lhs),
                            Some(rhs),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x89, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    // 	mov r/m64, r64
                    (_, Operand::Register(reg))
                        if lhs.is_rm() && lhs.size() == Size::_64 && lhs.size() == rhs.size() =>
                    {
                        Instruction::encode_rex_from_operands(w, true, Some(lhs), Some(rhs), None)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x89, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }

                    // mov r, rm
                    // Encoding: RM 	ModRM:reg (w) 	ModRM:r/m (r)
                    (Operand::Register(reg), _)
                        if rhs.is_rm() && reg.is_8_bits() && lhs.size() == rhs.size() =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            false,
                            Some(rhs),
                            Some(lhs),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(*reg));
                        w.write_all(&[0x8A, modrm])?;
                        if let Some(addr) = rhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (Operand::Register(reg), _)
                        if rhs.is_rm()
                            && (reg.is_16_bits() || reg.is_32_bits())
                            && lhs.size() == rhs.size() =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            false,
                            Some(rhs),
                            Some(lhs),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(*reg));
                        w.write_all(&[0x8B, modrm])?;
                        if let Some(addr) = rhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (Operand::Register(reg), _)
                        if rhs.is_rm() && reg.is_64_bits() && lhs.size() == rhs.size() =>
                    {
                        Instruction::encode_rex_from_operands(w, true, Some(rhs), Some(lhs), None)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(*reg));
                        w.write_all(&[0x8B, modrm])?;
                        if let Some(addr) = rhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }

                    // mov rm, imm
                    // Encoding: MI 	ModRM:r/m (w) 	imm8/16/32/64
                    (_, Operand::Immediate(imm)) if lhs.is_rm() && lhs.size() == Size::_8 => {
                        Instruction::encode_rex_from_operands(w, false, Some(lhs), None, None)?;

                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0xC6, modrm])?;
                        Instruction::encode_imm(w, *imm, &Size::_8)?;
                    }
                    (_, Operand::Immediate(imm)) if lhs.is_rm() && lhs.size() == Size::_16 => {
                        Instruction::encode_rex_from_operands(w, false, Some(lhs), None, None)?;

                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0xC7, modrm])?;
                        Instruction::encode_imm(w, *imm, &Size::_16)?;
                    }
                    (_, Operand::Immediate(imm)) if lhs.is_rm() && lhs.size() == Size::_32 => {
                        Instruction::encode_rex_from_operands(w, false, Some(lhs), None, None)?;

                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0xC7, modrm])?;
                        Instruction::encode_imm(w, *imm, &Size::_32)?;
                    }
                    // mov r/m64, imm32
                    (_, Operand::Immediate(imm))
                        if lhs.is_rm()
                            && lhs.size() == Size::_64
                            && ((i32::MIN as i64)..=(i32::MAX as i64)).contains(imm) =>
                    {
                        Instruction::encode_rex_from_operands(w, true, Some(lhs), None, None)?;

                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0xC7, modrm])?;
                        Instruction::encode_imm(w, *imm, &Size::_32)?;
                    }

                    _ => return Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
                Ok(())
            }
            InstructionKind::Add => {
                if self.operands.len() != 2 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let lhs = &self.operands[0];
                let rhs = &self.operands[1];

                match (lhs, rhs) {
                    // add al, imm8
                    (Operand::Register(Register::Al), Operand::Immediate(imm)) => {
                        w.write_all(&[0x04, *imm as u8])?;
                    }
                    // add ax, imm16
                    (Operand::Register(Register::Ax), Operand::Immediate(imm)) => {
                        w.write_all(&[0x05])?;
                        w.write_all(&(*imm as u16).to_le_bytes())?;
                    }
                    // add eax, imm32
                    (Operand::Register(Register::Eax), Operand::Immediate(imm)) => {
                        w.write_all(&[0x05])?;
                        w.write_all(&(*imm as u32).to_le_bytes())?;
                    }
                    // add rax, imm32
                    (Operand::Register(Register::Rax), Operand::Immediate(imm)) => {
                        if !((i32::MIN as i64)..=(i32::MAX as i64)).contains(imm) {
                            return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                        }
                        Instruction::encode_rex_from_operands(w, true, None, None, None)?;
                        w.write_all(&[0x05])?;
                        w.write_all(&(*imm as u32).to_le_bytes())?;
                    }

                    // add rm8, imm8
                    // Encoding: MI 	ModRM:r/m (r, w) 	imm8/16/32
                    (_, Operand::Immediate(imm)) if lhs.is_rm() && lhs.size() == Size::_8 => {
                        Instruction::encode_rex_from_operands(w, false, Some(lhs), None, None)?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0x80, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        Instruction::encode_imm(w, *imm, &lhs.size())?;
                    }
                    // add rm16, imm8
                    // add rm32, imm8
                    // add rm64, imm8
                    (_, Operand::Immediate(imm))
                        if lhs.is_rm()
                            && (lhs.size() == Size::_16
                                || lhs.size() == Size::_32
                                || lhs.size() == Size::_64)
                            && ((i8::MIN as i64)..=(i8::MAX as i64)).contains(imm) =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            lhs.size() == Size::_64,
                            Some(lhs),
                            None,
                            None,
                        )?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0x83, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }

                        Instruction::encode_imm(w, *imm, &Size::_8)?;
                    }
                    // add rm16, imm16
                    (_, Operand::Immediate(imm))
                        if lhs.is_rm()
                            && (lhs.size() == Size::_16)
                            && ((i16::MIN as i64)..=(i16::MAX as i64)).contains(imm) =>
                    {
                        Instruction::encode_rex_from_operands(w, false, Some(lhs), None, None)?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0x81, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }

                        Instruction::encode_imm(w, *imm, &lhs.size())?;
                    }
                    // add rm32, imm32
                    // add rm64, imm32
                    (_, Operand::Immediate(imm))
                        if lhs.is_rm()
                            && lhs.size() >= Size::_32
                            && ((i32::MIN as i64)..=(i32::MAX as i64)).contains(imm) =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            lhs.size() == Size::_64,
                            Some(lhs),
                            None,
                            None,
                        )?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, lhs, None);
                        w.write_all(&[0x81, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }

                        Instruction::encode_imm(w, *imm, &Size::_32)?;
                    }
                    // add rm, r
                    // Encoding: MR 	ModRM:r/m (r, w) 	ModRM:reg (r)
                    (_, Operand::Register(reg))
                        if lhs.is_rm() && lhs.size() == Size::_8 && lhs.size() == rhs.size() =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            false,
                            Some(lhs),
                            Some(rhs),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x00, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (_, Operand::Register(reg))
                        if lhs.is_rm()
                            && (lhs.size() == Size::_16
                                || lhs.size() == Size::_32
                                || lhs.size() == Size::_64)
                            && lhs.size() == rhs.size() =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            lhs.size() == Size::_64,
                            Some(lhs),
                            Some(rhs),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, lhs, Some(*reg));
                        w.write_all(&[0x01, modrm])?;
                        if let Some(addr) = lhs.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    _ => return Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
                Ok(())
            }
            InstructionKind::IMul => {
                if self.operands.is_empty() || self.operands.len() > 3 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let op1 = &self.operands[0];
                let op2 = self.operands.get(1);
                let op3 = self.operands.get(2);

                match (op1, op1.size(), op2, op3) {
                    // imul r, rm
                    // Encoding: RM 	ModRM:reg (r, w) 	ModRM:r/m (r)
                    (Operand::Register(reg), Size::_16, Some(op2), None)
                    | (Operand::Register(reg), Size::_32, Some(op2), None)
                        if op2.is_rm() && op2.size() == op1.size() && !op2.has_ambiguous_size() =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            false,
                            Some(op2),
                            Some(op1),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, op2, Some(*reg));
                        w.write_all(&[0x0f, 0xaf, modrm])?;
                        if let Some(addr) = op2.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (Operand::Register(reg), Size::_64, Some(op2), None)
                        if op2.is_rm() && op2.size() == op1.size() && !op2.has_ambiguous_size() =>
                    {
                        Instruction::encode_rex_from_operands(w, true, Some(op2), Some(op1), None)?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, op2, Some(*reg));
                        w.write_all(&[0x0f, 0xaf, modrm])?;
                        if let Some(addr) = op2.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    // imul rm
                    (_, Size::_8, None, None) if op1.is_rm() && !op1.has_ambiguous_size() => {
                        Instruction::encode_rex_from_operands(w, false, Some(op1), None, None)?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash5, op1, None);
                        w.write_all(&[0xf6, modrm])?;
                        if let Some(addr) = op1.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    (_, Size::_16 | Size::_32 | Size::_64, None, None)
                        if op1.is_rm() && !op1.has_ambiguous_size() =>
                    {
                        Instruction::encode_rex_from_operands(
                            w,
                            op1.size() == Size::_64,
                            Some(op1),
                            None,
                            None,
                        )?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash5, op1, None);
                        w.write_all(&[0xf7, modrm])?;
                        if let Some(addr) = op1.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                    }
                    // imul r, rm, imm8
                    (
                        Operand::Register(reg),
                        Size::_16 | Size::_32 | Size::_64,
                        Some(op2),
                        Some(Operand::Immediate(imm)),
                    ) if op2.is_rm() && op2.size() == op1.size() && !op2.has_ambiguous_size() => {
                        Instruction::encode_rex_from_operands(
                            w,
                            op1.size() == Size::_64,
                            Some(op2),
                            Some(op1),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, op2, Some(*reg));
                        w.write_all(&[0x6B, modrm])?;
                        if let Some(addr) = op2.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        w.write_all(&(*imm as u8).to_le_bytes())?;
                    }
                    // imul r16, rm, imm16
                    (
                        Operand::Register(reg),
                        Size::_16,
                        Some(op2),
                        Some(Operand::Immediate(imm)),
                    ) if op2.is_rm() && op2.size() == op1.size() && !op2.has_ambiguous_size() => {
                        Instruction::encode_rex_from_operands(
                            w,
                            false,
                            Some(op2),
                            Some(op1),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, op2, Some(*reg));
                        w.write_all(&[0x69, modrm])?;
                        if let Some(addr) = op2.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        w.write_all(&(*imm as u16).to_le_bytes())?;
                    }
                    // imul r32, rm, imm32
                    // imul r64, rm, imm32
                    (
                        Operand::Register(reg),
                        Size::_32 | Size::_64,
                        Some(op2),
                        Some(Operand::Immediate(imm)),
                    ) if op2.is_rm() && op2.size() == op1.size() && !op2.has_ambiguous_size() => {
                        Instruction::encode_rex_from_operands(
                            w,
                            op1.size() == Size::_64,
                            Some(op2),
                            Some(op1),
                            None,
                        )?;
                        let modrm =
                            Instruction::encode_modrm(ModRmEncoding::SlashR, op2, Some(*reg));
                        w.write_all(&[0x69, modrm])?;
                        if let Some(addr) = op2.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        w.write_all(&(*imm as u32).to_le_bytes())?;
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

                // Ambiguous?
                if matches!(
                    op,
                    Operand::EffectiveAddress(EffectiveAddress {
                        size_override: None,
                        ..
                    })
                ) {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let modrm = Instruction::encode_modrm(ModRmEncoding::Slash7, op, None);

                match (&op, op.size()) {
                    // idiv rm
                    // Encoding: M 	ModRM:r/m (r)
                    (_, Size::_8) if op.is_rm() => {
                        Instruction::encode_rex_from_operands(w, false, Some(op), None, None)?;
                        w.write_all(&[0xf6])?;
                        w.write_all(&[modrm])?;
                        if let Some(addr) = op.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        Ok(())
                    }
                    (_, Size::_16 | Size::_32 | Size::_64) if op.is_rm() => {
                        Instruction::encode_rex_from_operands(
                            w,
                            op.size() == Size::_64,
                            Some(op),
                            None,
                            None,
                        )?;
                        w.write_all(&[0xf7])?;
                        w.write_all(&[modrm])?;
                        if let Some(addr) = op.as_effective_address() {
                            Instruction::encode_sib(w, &addr, modrm)?;
                        }
                        Ok(())
                    }
                    _ => Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
            }
            // lea r, m
            // Encoding: RM 	ModRM:reg (w) 	ModRM:r/m (r)
            InstructionKind::Lea => {
                if self.operands.len() != 2 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let lhs = self.operands.first().unwrap();
                let rhs = self.operands.get(1).unwrap();

                if lhs.size() == Size::_8 {
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

                Instruction::encode_rex_from_operands(
                    w,
                    lhs.size() == Size::_64,
                    Some(rhs),
                    Some(lhs),
                    None,
                )?;

                let opcode = 0x8d;
                w.write_all(&[opcode])?;

                let modrm = Instruction::encode_modrm(ModRmEncoding::SlashR, rhs, Some(reg));
                w.write_all(&[modrm])?;

                Instruction::encode_sib(w, &addr, modrm)
            }
            InstructionKind::Call => {
                if self.operands.len() != 1 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }
                let name = self.operands.first().unwrap().as_fn_name().unwrap();
                let location = symbols
                    .get(name)
                    .expect("function location not found")
                    .location;
                let displacement = (w.len() + 5/* sizeof(call_ins_encoded) */)
                    .checked_sub(location)
                    .unwrap() as isize;
                let disp32 = i32::try_from(displacement.neg()).expect("function too far");
                w.write_all(&[0xe8])?; // Call near.
                w.write_all(&disp32.to_le_bytes())
            }
            InstructionKind::Push => {
                if self.operands.len() != 1 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let op = self.operands.first().unwrap();
                if op.size() == Size::_8 || op.size() == Size::_32 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }
                match op {
                    // push r
                    // Encoding: O 	opcode + rd (r)
                    Operand::Register(reg) => {
                        if reg.is_extended() {
                            Instruction::encode_rex_from_operands(w, false, None, None, Some(op))?;
                        }
                        w.write_all(&[0x50 | reg.to_3_bits()])
                    }
                    // push imm
                    // Encoding: I 	imm8/16/32
                    Operand::Immediate(imm) => {
                        if let Ok(imm) = u8::try_from(*imm) {
                            w.write_all(&[0x6A])?;
                            w.write_all(&imm.to_le_bytes())?;
                        }
                        // In theory there is a "push imm16" rule but for reasons,
                        // we use "push imm32".
                        else if let Ok(imm) = u32::try_from(*imm) {
                            w.write_all(&[0x68])?;
                            w.write_all(&imm.to_le_bytes())?;
                        } else {
                            return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                        }
                        Ok(())
                    }
                    // push rm
                    // Encoding: M 	ModRM:r/m (r)
                    Operand::EffectiveAddress(addr) => {
                        Instruction::encode_rex_from_operands(w, false, Some(op), None, None)?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash6, op, None);
                        w.write_all(&[0xff, modrm])?;
                        Instruction::encode_sib(w, addr, modrm)
                    }
                    _ => Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
            }
            InstructionKind::Pop => {
                if self.operands.len() != 1 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }

                let op = self.operands.first().unwrap();
                if op.size() == Size::_8 || op.size() == Size::_32 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }
                match op {
                    // pop r16
                    // pop r64
                    // Encoding: O 	opcode + rd (w)
                    Operand::Register(reg) => {
                        if reg.is_extended() {
                            Instruction::encode_rex_from_operands(
                                w,
                                reg.size() == Size::_64,
                                None,
                                None,
                                Some(op),
                            )?;
                        }

                        w.write_all(&[0x58 | reg.to_3_bits()])
                    }
                    // pop rm
                    // Encoding: M 	ModRM:r/m (w)
                    Operand::EffectiveAddress(addr) => {
                        if op.size() == Size::_8 {
                            return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                        }

                        Instruction::encode_rex_from_operands(w, false, Some(op), None, None)?;
                        let modrm = Instruction::encode_modrm(ModRmEncoding::Slash0, op, None);
                        w.write_all(&[0x8f, modrm])?;
                        Instruction::encode_sib(w, addr, modrm)
                    }
                    _ => Err(std::io::Error::from(io::ErrorKind::InvalidData)),
                }
            }
            InstructionKind::Syscall => {
                if !self.operands.is_empty() {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }
                w.write_all(&[0x0f, 0x05])
            }
            InstructionKind::Ret => {
                if self.operands.len() > 1 {
                    return Err(std::io::Error::from(io::ErrorKind::InvalidData));
                }
                if self.operands.is_empty() {
                    return w.write_all(&[0xC3]); // Near return.
                }

                let op = self.operands.first().unwrap();
                if let Some(imm) = op.as_imm() {
                    w.write_all(&[0xC2])?;
                    w.write_all(&(imm as u16).to_le_bytes())
                } else {
                    Err(std::io::Error::from(io::ErrorKind::InvalidData))
                }
            }
        }
    }
}

impl Operand {
    pub(crate) fn is_reg(&self) -> bool {
        matches!(self, Operand::Register(_))
    }

    pub(crate) fn is_effective_address(&self) -> bool {
        matches!(self, Operand::EffectiveAddress(_))
    }

    pub(crate) fn has_ambiguous_size(&self) -> bool {
        matches!(
            self,
            Operand::EffectiveAddress(EffectiveAddress {
                size_override: None,
                ..
            })
        )
    }

    pub(crate) fn is_rm(&self) -> bool {
        self.is_reg() || self.is_effective_address()
    }

    pub(crate) fn as_reg(&self) -> Option<Register> {
        match self {
            Operand::Register(reg) => Some(*reg),
            _ => None,
        }
    }

    pub(crate) fn as_effective_address(&self) -> Option<EffectiveAddress> {
        match self {
            Operand::EffectiveAddress(addr) => Some(*addr),
            _ => None,
        }
    }

    pub(crate) fn as_imm(&self) -> Option<i64> {
        match self {
            Operand::Immediate(imm) => Some(*imm),
            _ => None,
        }
    }

    pub(crate) fn as_fn_name(&self) -> Option<&str> {
        match self {
            Operand::FnName(name) => Some(name),
            _ => None,
        }
    }

    fn size(&self) -> Size {
        match self {
            Operand::Register(reg) => reg.size(),
            Operand::Immediate(_) => Size::_64,
            Operand::EffectiveAddress(effective_address) => {
                effective_address.size_override.unwrap_or(Size::_64)
            }
            Operand::FnName(_) => Size::_64,
        }
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

impl From<&MemoryLocation> for Operand {
    fn from(value: &MemoryLocation) -> Self {
        match value {
            MemoryLocation::Register(asm::Register::Amd64(reg)) => Operand::Register(*reg),
            MemoryLocation::Stack(off) => Operand::EffectiveAddress(EffectiveAddress {
                base: Some(Register::Rsp),
                index_scale: None,
                displacement: (*off).try_into().unwrap(), // TODO: handle gracefully,
                size_override: None,
            }),
        }
    }
}

impl From<MemoryLocation> for Operand {
    fn from(value: MemoryLocation) -> Self {
        (&value).into()
    }
}

impl From<Operand> for MemoryLocation {
    fn from(value: Operand) -> Self {
        (&value).into()
    }
}

impl From<&Operand> for MemoryLocation {
    fn from(value: &Operand) -> Self {
        match value {
            Operand::Register(register) => {
                MemoryLocation::Register(asm::Register::Amd64(*register))
            }
            Operand::Immediate(_imm) => panic!(),
            Operand::EffectiveAddress(EffectiveAddress {
                base: Some(Register::Rsp),
                displacement,
                ..
            }) => MemoryLocation::Stack(*displacement as isize),
            Operand::EffectiveAddress(_) => todo!(),
            Operand::FnName(_) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::process::{ExitStatus, Stdio};

    use proptest::prelude::*;

    use super::*;

    #[test]
    fn test_encoding() {
        {
            let ins = Instruction {
                kind: InstructionKind::Mov,
                operands: vec![
                    Operand::Register(Register::Rdi),
                    Operand::EffectiveAddress(EffectiveAddress {
                        base: Some(Register::Rsp),
                        index_scale: None,
                        displacement: -8,
                        size_override: None,
                    }),
                ],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(8);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x48, 0x8b, 0x7c, 0x24, 0xf8]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Mov,
                operands: vec![
                    Operand::EffectiveAddress(EffectiveAddress {
                        base: Some(Register::Rsp),
                        index_scale: None,
                        displacement: -8,
                        size_override: None,
                    }),
                    Operand::Register(Register::Rdi),
                ],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(8);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x48, 0x89, 0x7c, 0x24, 0xf8]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Mov,
                operands: vec![Operand::Register(Register::Rax), Operand::Immediate(1)],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(8);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x48, 0xc7, 0xc0, 0x01, 0x00, 0x00, 0x00]);
        }
        {
            let mut w = Vec::with_capacity(15);

            let mut symbols = BTreeMap::new();

            symbols.insert(
                String::from("builtin.println_u64"),
                Symbol {
                    location: w.len(),
                    visibility: asm::Visibility::Local,
                    origin: Origin::new_builtin(),
                },
            );
            {
                let ins_mov = Instruction {
                    kind: InstructionKind::Mov,
                    operands: vec![Operand::Register(Register::Edx), Operand::Immediate(1)],
                    origin: Origin::new_unknown(),
                };
                ins_mov.encode(&mut w, &symbols).unwrap();

                let ins_ret = Instruction {
                    kind: InstructionKind::Ret,
                    operands: vec![],
                    origin: Origin::new_unknown(),
                };
                ins_ret.encode(&mut w, &symbols).unwrap();
            }

            {
                let ins_call = Instruction {
                    kind: InstructionKind::Call,
                    operands: vec![Operand::FnName(String::from("builtin.println_u64"))],
                    origin: Origin::new_unknown(),
                };
                ins_call.encode(&mut w, &symbols).unwrap();
            }

            assert_eq!(
                &w,
                &[
                    0xba, 0x01, 0x00, 0x00, 0x00, // mov edx, 1
                    0xc3, // ret
                    0xe8, 0xf5, 0xff, 0xff, 0xff // call println_u64
                ]
            );
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Add,
                operands: vec![
                    Operand::EffectiveAddress(EffectiveAddress {
                        base: Some(Register::Ebx),
                        index_scale: None,
                        displacement: 0,
                        size_override: Some(Size::_32),
                    }),
                    Operand::Immediate(4294967296),
                ],
                origin: Origin::new_unknown(),
            };
            let symbols = BTreeMap::new();
            let mut w = Vec::new();
            // Error on overflow.
            assert!(ins.encode(&mut w, &symbols).is_err());
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Add,
                operands: vec![Operand::Register(Register::Bx), Operand::Immediate(0)],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x66, 0x83, 0xc3, 0x00]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::IMul,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(Register::Ebx),
                    index_scale: None,
                    displacement: -129,
                    size_override: Some(Size::_8),
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(15);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x67, 0xf6, 0xab, 0x7f, 0xff, 0xff, 0xff]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Push,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: None,
                    index_scale: Some((Register::Ebx, Scale::_1)),
                    displacement: 1,
                    size_override: None,
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x67, 0xff, 0x73, 0x01]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Push,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(Register::Ebx),
                    index_scale: None,
                    displacement: 0,
                    size_override: None,
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x67, 0xff, 0x33]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Push,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: None,
                    index_scale: Some((Register::Ebx, Scale::_1)),
                    displacement: 0,
                    size_override: None,
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x67, 0xff, 0x33]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Push,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: None,
                    index_scale: Some((Register::Ebx, Scale::_2)),
                    displacement: 0,
                    size_override: Some(Size::_16),
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x67, 0x66, 0xff, 0x34, 0x5d, 0, 0, 0, 0]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Push,
                operands: vec![Operand::Register(Register::R15)],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(2);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x41, 0x57]);
        }

        {
            let ins = Instruction {
                kind: InstructionKind::Pop,
                operands: vec![Operand::Register(Register::Rbx)],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(2);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x5b]);
        }

        {
            let ins = Instruction {
                kind: InstructionKind::Lea,
                operands: vec![
                    Operand::Register(Register::R8),
                    Operand::EffectiveAddress(EffectiveAddress {
                        base: Some(Register::R13),
                        index_scale: Some((Register::R14, Scale::_8)),
                        displacement: 42,
                        size_override: None,
                    }),
                ],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x4f, 0x8d, 0x44, 0xf5, 0x2a]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Push,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(Register::R12),
                    index_scale: Some((Register::Rbx, Scale::_4)),
                    displacement: 1,
                    size_override: None,
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x41, 0xff, 0x74, 0x9c, 0x01]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Pop,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(Register::R12),
                    index_scale: Some((Register::Rbx, Scale::_4)),
                    displacement: 1,
                    size_override: None,
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x41, 0x8f, 0x44, 0x9c, 0x01]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::IDiv,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(Register::R12),
                    index_scale: Some((Register::Rbx, Scale::_4)),
                    displacement: 1,
                    size_override: None,
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::new();
            let symbols = BTreeMap::new();
            // Error due to ambiguous size.
            assert!(ins.encode(&mut w, &symbols).is_err());
        }
        {
            let ins = Instruction {
                kind: InstructionKind::IDiv,
                operands: vec![Operand::EffectiveAddress(EffectiveAddress {
                    base: Some(Register::R12),
                    index_scale: Some((Register::Rbx, Scale::_4)),
                    displacement: 1,
                    size_override: Some(Size::_64),
                })],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x49, 0xf7, 0x7c, 0x9c, 0x01]);
        }
        {
            let ins = Instruction {
                kind: InstructionKind::Mov,
                operands: vec![
                    Operand::Register(Register::Rbp),
                    Operand::Register(Register::Rsp),
                ],
                origin: Origin::new_unknown(),
            };
            let mut w = Vec::with_capacity(5);
            let symbols = BTreeMap::new();
            ins.encode(&mut w, &symbols).unwrap();
            assert_eq!(&w, &[0x48, 0x89, 0xe5]);
        }
    }

    fn oracle_encode(ins: &Instruction) -> Result<Vec<u8>, (ExitStatus, String, Vec<u8>)> {
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
                "-Wl,--build-id=none", // no build id.
                "-o",
                "/dev/stdout", // FIXME: Windows.
                "-",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|err| {
                (
                    ExitStatus::default(),
                    String::new(),
                    format!("{}", err).as_bytes().to_vec(),
                )
            })?;

        {
            let mut stdin = child.stdin.take().unwrap();
            write!(&mut stdin, "{}", ins).map_err(|err| {
                (
                    ExitStatus::default(),
                    String::new(),
                    format!("{}", err).as_bytes().to_vec(),
                )
            })?;
        }
        let output = child.wait_with_output().map_err(|err| {
            (
                ExitStatus::default(),
                String::new(),
                format!("{}", err).as_bytes().to_vec(),
            )
        })?;

        if output.status.success() {
            Ok(output.stdout)
        } else {
            Err((
                output.status,
                String::from_utf8_lossy(&output.stdout).to_string(),
                output.stderr,
            ))
        }
    }

    prop_compose! {
        fn arb_instruction()(
            kind in any::<InstructionKind>(),
            // Generates a Vec of Operand with size between 0 and 2
            operands in prop::collection::vec(any::<Operand>(), 0..=2)
        ) -> Instruction {
            Instruction { kind, operands , origin:Origin::new_unknown()}
        }
    }

    proptest! {
      #[test]
      fn test_encode_proptest(ins in arb_instruction()){
          // Skip malformed effective addresses (if any).
          let has_invalid_addresses = ins.operands.iter().any(|op| if let Some(addr) = op.as_effective_address() && !addr.is_valid() { return true; } else {false});

          if !has_invalid_addresses {
            let mut actual = Vec::with_capacity(15);

            let symbols = BTreeMap::new();
            match (ins.encode(&mut actual, &symbols), oracle_encode(&ins)) {
                (Ok(()), Ok(expected)) => assert_eq!(actual, expected, "ins={}, {:#?} actual={:x?} expected={:x?}", ins,ins, &actual, &expected),
                (Err(_), Err(_)) => {},
                (Ok(actual),Err((status, stdout, stderr))) => panic!("oracle and implementation disagree: actual={:#?} oracle_status={} oracle_stdout={} oracle_stderr={} ins={} {:#?}",actual,status,stdout, String::from_utf8_lossy(&stderr), ins,ins ),
                (Err(actual),Ok(oracle)) => panic!("oracle and implementation disagree: actual={:#?} oracle={:x?} ins={} {:#?}",actual,&oracle, ins,ins ),
            }
          }
      }
    }
}
