use serde::Serialize;

pub enum ArchKind {
    Amd64,
    // TODO
}

pub struct Abi {
    arch_kind: ArchKind,
    // TODO
}

#[derive(Serialize, Debug)]
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
        asm::OperandSize,
        ir::{self},
        origin::Origin,
        register_alloc::{MemoryLocation, RegAlloc},
    };

    #[derive(Serialize, Debug)]
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

    #[derive(Serialize, Debug)]
    pub enum InstructionKind {
        Mov,
        Add,
    }

    #[derive(Serialize, Debug)]
    pub enum OperandKind {
        Register(Register),
        Immediate(u64),
    }

    #[derive(Serialize, Debug)]
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

    fn ir_operand_to_asm(op: &Option<ir::Operand>, regalloc: &RegAlloc) -> Option<Operand> {
        match op {
            Some(ir::Operand::VReg(vreg)) => {
                let memory_location = regalloc.get(vreg).unwrap();
                let kind = match memory_location {
                    MemoryLocation::Register(register) => OperandKind::Register(register),
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

    impl Emitter {
        pub fn new() -> Self {
            Self {
                instructions: Vec::new(),
            }
        }

        pub fn emit(&mut self, irs: &[ir::Instruction], regalloc: &RegAlloc) {
            self.instructions.reserve(irs.len());

            for ir in irs {
                let lhs = ir_operand_to_asm(&ir.lhs, regalloc);
                let rhs = ir_operand_to_asm(&ir.lhs, regalloc);

                match ir.kind {
                    ir::InstructionKind::Add => {
                        let ins = Instruction {
                            kind: InstructionKind::Add,
                            lhs,
                            rhs,
                            origin: ir.origin,
                        };
                        self.instructions.push(ins);
                    }
                    ir::InstructionKind::Set => {
                        let ins = Instruction {
                            kind: InstructionKind::Mov,
                            lhs,
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
