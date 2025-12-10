use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::{
    asm::{self, Abi, Operand, Register},
    ir::{self, Lifetimes, VirtualRegister},
};

#[derive(Serialize, Debug)]
pub enum MemoryLocation {
    Register(Register),
    Stack(u32), // Stack offset.
}

pub type RegisterMapping = BTreeMap<VirtualRegister, MemoryLocation>;

// TODO: Constraints.
pub(crate) fn regalloc(
    vcode: &[asm::VInstruction],
    _lifetimes: &Lifetimes,
    abi: &Abi,
) -> (Vec<asm::Instruction>, RegisterMapping) {
    let mut vreg_to_memory_location = RegisterMapping::new();
    let mut instructions = Vec::with_capacity(vcode.len());

    let mut free_registers = BTreeSet::<Register>::new();
    for register in &abi.gprs {
        free_registers.insert(*register);
    }

    for vins in vcode {
        let in_out = vins.kind.get_in_out();

        let dst = match vins.dst {
            Some(ir::Operand::VirtualRegister(vreg)) => {
                let preg = in_out.get_fixed_output_reg().unwrap_or_else(|| {
                    free_registers
                        .pop_first()
                        .expect("need to spill - not yet implemented")
                });
                vreg_to_memory_location.insert(vreg, MemoryLocation::Register(preg));

                Some(Operand {
                    operand_size: asm::OperandSize::Eight,
                    kind: asm::OperandKind::Register(preg),
                })
            }
            Some(ir::Operand::Num(_)) => panic!("invalid number as instruction destination"),
            None => None,
        };

        let operands = vins
            .operands
            .iter()
            .map(|op| match op {
                ir::Operand::VirtualRegister(vreg) => {
                    let preg = in_out.get_fixed_input_reg().unwrap_or_else(|| {
                        free_registers
                            .pop_first()
                            .expect("need to spill - not yet implemented")
                    });
                    vreg_to_memory_location.insert(*vreg, MemoryLocation::Register(preg));

                    Operand {
                        operand_size: asm::OperandSize::Eight,
                        kind: asm::OperandKind::Register(preg),
                    }
                }
                ir::Operand::Num(num) => Operand {
                    operand_size: asm::OperandSize::Eight,
                    kind: asm::OperandKind::Immediate(*num),
                },
            })
            .collect::<Vec<Operand>>();

        let ins = asm::Instruction {
            kind: vins.kind,
            dst,
            operands,
            origin: vins.origin,
        };
        instructions.push(ins);
    }

    //let mut active = BTreeSet::<usize>::new();
    //let mut lifetimes_start_asc = lifetimes.iter().collect::<Vec<_>>();
    //lifetimes_start_asc.sort_by(|(_, a), (_, b)| a.start.cmp(&b.start));
    //
    //let mut lifetimes_end_desc: Vec<_> = lifetimes_start_asc.clone();
    //lifetimes_end_desc.sort_by(|(_, a), (_, b)| b.end.cmp(&a.end));
    //
    //for (i, (vreg, _lifetime)) in lifetimes_start_asc.iter().enumerate() {
    //    expire_old_intervals(
    //        i,
    //        &lifetimes_start_asc,
    //        &lifetimes_end_desc,
    //        &mut active,
    //        &mut free_registers,
    //        &res,
    //    );
    //
    //    if active.len() == abi.gprs.len() {
    //        spill_at_interval(i, &lifetimes_end_desc, &mut active);
    //    } else {
    //        let free_register = free_registers.pop_first().unwrap();
    //        res.insert(**vreg, MemoryLocation::Register(free_register));
    //        active.insert(i);
    //    }
    //}

    (instructions, vreg_to_memory_location)
}

//fn expire_old_intervals(
//    pos: usize,
//    lifetimes_start_asc: &[(&VirtualRegister, &Lifetime)],
//    lifetimes_end_desc: &[(&VirtualRegister, &Lifetime)],
//    active: &mut BTreeSet<usize>,
//    free_registers: &mut BTreeSet<Register>,
//    regalloc: &RegAlloc,
//) {
//    assert_eq!(lifetimes_start_asc.len(), lifetimes_end_desc.len());
//
//    for (j, (vreg, lifetime)) in lifetimes_end_desc.iter().enumerate() {
//        let end = lifetime.end;
//        let start = lifetimes_start_asc[pos].1.start;
//        if end >= start {
//            return;
//        }
//        active.remove(&j);
//        let register = match regalloc[vreg] {
//            MemoryLocation::Register(reg) => reg,
//            _ => panic!("should be assigned a register"),
//        };
//        free_registers.insert(register);
//    }
//}
//
//fn spill_at_interval(
//    pos: usize,
//    lifetimes_end_desc: &[(&VirtualRegister, &Lifetime)],
//    active: &mut BTreeSet<usize>,
//) {
//    let spill_interval = *active.last().unwrap();
//    if lifetimes_end_desc[spill_interval].1.end > lifetimes_end_desc[pos].1.end {
//        todo!()
//    } else {
//        todo!()
//    }
//}
