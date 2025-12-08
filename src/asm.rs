use serde::Serialize;

use crate::register_alloc::Register;

pub enum ArchKind {
    Amd64,
    // TODO
}

pub struct Abi {
    pub arch_kind: ArchKind,
    pub gprs: Vec<Register>,
}

#[derive(Serialize, Debug, Clone, Copy)]
enum OperandSize {
    One = 1,
    Two = 2,
    Four = 4,
    Eight = 8,
}

pub mod amd64 {
    use std::io::Write;

    use serde::Serialize;

    use crate::{
        asm::{Abi, OperandSize},
        ir::{self},
        origin::Origin,
        register_alloc::{MemoryLocation, RegAlloc},
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

    impl From<&super::Register> for Register {
        fn from(value: &super::Register) -> Self {
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
    impl From<&Register> for super::Register {
        fn from(value: &Register) -> Self {
            super::Register(*value as u8)
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
            arch_kind: super::ArchKind::Amd64,
            gprs: GPRS.iter().map(|r| r.into()).collect(),
        }
    }

    #[derive(Serialize, Debug)]
    pub enum InstructionKind {
        Mov,
        Add,
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

    pub struct Emitter {
        pub instructions: Vec<Instruction>,
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
            Some(ir::Operand::VReg(vreg)) => {
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
                    ir::InstructionKind::Add => {
                        let res_location = regalloc.get(&ir.res_vreg).unwrap();
                        let res_operand = memory_location_to_asm_operand(res_location);
                        let rhs_mov = ir_operand_to_asm(&ir.lhs, regalloc);

                        let ins_mov = Instruction {
                            kind: InstructionKind::Mov,
                            lhs: Some(res_operand.clone()),
                            rhs: rhs_mov,
                            origin: ir.origin,
                        };
                        self.instructions.push(ins_mov);

                        let rhs_add = ir_operand_to_asm(&ir.rhs, regalloc);

                        let ins_add = Instruction {
                            kind: InstructionKind::Add,
                            lhs: Some(res_operand),
                            rhs: rhs_add,
                            origin: ir.origin,
                        };
                        self.instructions.push(ins_add);
                    }
                    ir::InstructionKind::Set => {
                        let res_location = regalloc.get(&ir.res_vreg).unwrap();
                        let res_operand = memory_location_to_asm_operand(res_location);
                        let rhs = ir_operand_to_asm(&ir.rhs, regalloc);
                        let ins = Instruction {
                            kind: InstructionKind::Mov,
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
                InstructionKind::Mov => {
                    write!(w, "mov ")?;

                    if let Some(lhs) = &self.lhs {
                        lhs.write(w)?;
                    }
                    write!(w, ", ")?;

                    if let Some(rhs) = &self.rhs {
                        rhs.write(w)?;
                    }
                }
                InstructionKind::Add => {
                    write!(w, "add ")?;

                    if let Some(lhs) = &self.lhs {
                        lhs.write(w)?;
                    }
                    write!(w, ", ")?;

                    if let Some(rhs) = &self.rhs {
                        rhs.write(w)?;
                    }
                }
            }

            writeln!(w)
        }
    }
}
