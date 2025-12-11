use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::{
    asm::{self, Abi, InstructionInOutOperand, Operand, Register},
    ir::{self, LiveRange, LiveRanges, VirtualRegister},
};

#[derive(Serialize, Debug, Hash, PartialEq, Eq)]
pub enum MemoryLocation {
    Register(Register),
    Stack(u32), // Stack offset.
}

pub type RegisterMapping = BTreeMap<VirtualRegister, MemoryLocation>;

fn precoloring(vcode: &[asm::VInstruction], abi: &Abi) -> (RegisterMapping, BTreeSet<Register>) {
    let mut vreg_to_memory_location = RegisterMapping::new();

    let mut free_registers = BTreeSet::<Register>::new();
    for register in &abi.gprs {
        free_registers.insert(*register);
    }

    for vins in vcode {
        let in_out = vins.kind.get_in_out();

        match vins.dst {
            Some(ir::Operand::VirtualRegister(vreg)) => {
                if let Some(preg) = in_out.get_fixed_output_reg() {
                    let present = free_registers.remove(&preg);
                    assert!(present);

                    assert!(
                        vreg_to_memory_location
                            .insert(vreg, MemoryLocation::Register(preg))
                            .is_none()
                    );
                }
            }
            Some(ir::Operand::Num(_)) => panic!("invalid number as instruction destination"),
            None => {}
        };

        for op in &vins.operands {
            match op {
                ir::Operand::VirtualRegister(vreg) => {
                    for rr in &in_out.registers_read {
                        if let InstructionInOutOperand::FixedRegister(r) = rr {
                            let present = free_registers.remove(r);
                            assert!(present);

                            assert!(
                                vreg_to_memory_location
                                    .insert(*vreg, MemoryLocation::Register(*r))
                                    .is_none()
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }

    (vreg_to_memory_location, free_registers)
}

// TODO: Constraints.
pub(crate) fn regalloc(
    vcode: &[asm::VInstruction],
    live_ranges: &LiveRanges,
    abi: &Abi,
) -> (Vec<asm::Instruction>, RegisterMapping) {
    let mut instructions = Vec::with_capacity(vcode.len());

    let (mut vreg_to_memory_location, mut free_registers) = precoloring(vcode, abi);

    //for vins in vcode {
    //    let dst = match vins.dst {
    //        Some(ir::Operand::VirtualRegister(vreg)) => {
    //            let preg = if let Some(MemoryLocation::Register(preg)) =
    //                vreg_to_memory_location.get(&vreg)
    //            {
    //                *preg
    //            } else {
    //                free_registers
    //                    .pop_first()
    //                    .expect("need to spill - not yet implemented")
    //            };
    //            vreg_to_memory_location.insert(vreg, MemoryLocation::Register(preg));
    //
    //            Some(Operand {
    //                operand_size: asm::OperandSize::Eight,
    //                kind: asm::OperandKind::Register(preg),
    //            })
    //        }
    //        Some(ir::Operand::Num(_)) => panic!("invalid number as instruction destination"),
    //        None => None,
    //    };
    //
    //    let operands = vins
    //        .operands
    //        .iter()
    //        .map(|op| match op {
    //            ir::Operand::VirtualRegister(vreg) => {
    //                let preg = if let Some(MemoryLocation::Register(preg)) =
    //                    vreg_to_memory_location.get(&vreg)
    //                {
    //                    *preg
    //                } else {
    //                    todo!();
    //                };
    //                vreg_to_memory_location.insert(*vreg, MemoryLocation::Register(preg));
    //
    //                Operand {
    //                    operand_size: asm::OperandSize::Eight,
    //                    kind: asm::OperandKind::Register(preg),
    //                }
    //            }
    //            ir::Operand::Num(num) => Operand {
    //                operand_size: asm::OperandSize::Eight,
    //                kind: asm::OperandKind::Immediate(*num),
    //            },
    //        })
    //        .collect::<Vec<Operand>>();
    //
    //    let ins = asm::Instruction {
    //        kind: vins.kind,
    //        dst,
    //        operands,
    //        origin: vins.origin,
    //    };
    //    instructions.push(ins);
    //}

    // Source: https://dl.acm.org/doi/pdf/10.1145/330249.330250
    // LinearScanRegisterAllocation
    //     active ← {}
    //     foreach live interval i, in order of increasing start point
    //         ExpireOldIntervals(i)
    //         if length(active) = R then
    //             SpillAtInterval(i)
    //         else
    //             register[i] ← a register removed from pool of free registers
    //             add i to active, sorted by increasing end point

    // Sorted by the end of the live range, descending.
    let mut active = Vec::<(VirtualRegister, LiveRange)>::with_capacity(abi.gprs.len());

    // Sorted by the start of the live range, ascending.
    let mut live_ranges_start_asc = live_ranges
        .iter()
        .map(|(vreg, range)| (*vreg, *range))
        .collect::<Vec<(VirtualRegister, LiveRange)>>();
    live_ranges_start_asc.sort_by(|(_, a), (_, b)| a.start.cmp(&b.start));

    for vreg_range in &live_ranges_start_asc {
        assert!(active.len() <= abi.gprs.len());

        active = expire_old_intervals(
            &vreg_range.1,
            &active,
            &mut free_registers,
            &vreg_to_memory_location,
        );

        assert!(active.len() <= abi.gprs.len());

        // Already filled by pre-coloring?
        if vreg_to_memory_location.get(&vreg_range.0).is_some() {
            insert_sorted(&mut active, *vreg_range);
            continue;
        }

        if active.len() == abi.gprs.len() {
            spill_at_interval(&vreg_range.1, &mut active);
        } else {
            // TODO: We could have a heuristic here instead of just 'the first free register'.
            let free_register = free_registers.pop_first().unwrap();
            vreg_to_memory_location.insert(vreg_range.0, MemoryLocation::Register(free_register));
            insert_sorted(&mut active, *vreg_range);
        }
    }

    (instructions, vreg_to_memory_location)
}

// ExpireOldIntervals(i)
//     foreach interval j in active, in order of increasing end point
//         if endpoint[j] ≥ startpoint[i] then
//             return
//         remove j from active
//         add register[j] to pool of free registers
fn expire_old_intervals(
    live_range_at: &LiveRange,
    active: &[(VirtualRegister, LiveRange)],
    free_registers: &mut BTreeSet<Register>,
    vreg_to_memory_location: &RegisterMapping,
) -> Vec<(VirtualRegister, LiveRange)> {
    let mut new_active = active.to_vec();

    for (vreg, live_range) in active {
        if live_range.end >= live_range_at.start {
            break;
        }

        // TODO: Could probably be optimized?
        new_active = new_active
            .extract_if(.., |&mut e| &e.1 == live_range)
            .collect();

        if let MemoryLocation::Register(preg) = vreg_to_memory_location[vreg] {
            free_registers.insert(preg);
        };
    }

    new_active
}

// SpillAtInterval(i)
//     spill ← last interval in active
//     if endpoint[spill] > endpoint[i] then
//         register[i] ← register[spill]
//         location[spill] ← new stack location
//         remove spill from active
//         add i to active, sorted by increasing end point
//     else
//         location[i] ← new stack location
fn spill_at_interval(_live_range_at: &LiveRange, _active: &mut Vec<(VirtualRegister, LiveRange)>) {
    todo!();
}

fn insert_sorted(
    active: &mut Vec<(VirtualRegister, LiveRange)>,
    item: (VirtualRegister, LiveRange),
) {
    match active.binary_search_by(|(_, range)| range.end.cmp(&item.1.end)) {
        Ok(_pos) => {
            panic!("element already present")
        }
        Err(pos) => active.insert(pos, item),
    }
}
