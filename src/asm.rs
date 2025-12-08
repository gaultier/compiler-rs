use serde::Serialize;

pub enum ArchKind {
    Amd64,
    // TODO
}

//pub struct Register(u8);

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

    use crate::{asm::OperandSize, ir, origin::Origin};

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

    impl Emitter {
        pub fn new() -> Self {
            Self {
                instructions: Vec::new(),
            }
        }

        pub fn emit(&mut self, irs: &[ir::Instruction]) {
            self.instructions.reserve(irs.len());

            for ir in irs {
                match ir.kind {
                    ir::InstructionKind::Add => {
                        let ins = Instruction {
                            kind: InstructionKind::Add,
                            lhs: Some(Operand {
                                operand_size: OperandSize::Eight,
                                kind: OperandKind::Register(Register::Rax), // FIXME
                            }),
                            rhs: Some(Operand {
                                operand_size: OperandSize::Eight,
                                kind: OperandKind::Register(Register::R8), // FIXME
                            }),
                            origin: ir.origin,
                        };
                        self.instructions.push(ins);
                    }
                    ir::InstructionKind::Set => {
                        let ins = Instruction {
                            kind: InstructionKind::Mov,
                            lhs: Some(Operand {
                                operand_size: OperandSize::Eight,
                                kind: OperandKind::Register(Register::Rax), // FIXME
                            }),
                            rhs: Some(Operand {
                                operand_size: OperandSize::Eight,
                                kind: OperandKind::Immediate(69), // FIXME
                            }),
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
