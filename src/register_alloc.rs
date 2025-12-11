use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::{
    asm::{
        self, Abi, Register,
        format::{Location, Operand},
    },
    ir::{self, LiveRange, LiveRanges, VirtualRegister},
};

#[derive(Serialize, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

    // TODO

    //for vins in vcode {
    //    let in_out = vins.kind.get_in_out();
    //    for op in &vins.operands {
    //        if let ir::Operand::VirtualRegister(vreg) = op {
    //            for fmt_op in &in_out {
    //                match fmt_op {
    //                    Operand {
    //                        location: Location::Rax,
    //                        mutability,
    //                        implicit,
    //                    } => {}
    //                }
    //            }
    //        }
    //    }
    //
    //    match vins.operands.first() {
    //        Some(ir::Operand::VirtualRegister(vreg)) => {
    //            if let Some(preg) = in_out.get_fixed_output_reg() {
    //                free_registers.remove(&preg);
    //                vreg_to_memory_location.insert(*vreg, MemoryLocation::Register(preg));
    //            }
    //        }
    //        Some(ir::Operand::Num(_)) => panic!("invalid number as instruction destination"),
    //        None => {}
    //    };
    //}

    (vreg_to_memory_location, free_registers)
}

// TODO: Constraints.
pub(crate) fn regalloc(
    vcode: &[asm::VInstruction],
    live_ranges: &LiveRanges,
    abi: &Abi,
) -> RegisterMapping {
    let (mut vreg_to_memory_location, mut free_registers) = precoloring(vcode, abi);

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
        assert!(free_registers.len() <= abi.gprs.len());
        assert!(active.len() <= abi.gprs.len());
        assert!(active.is_sorted_by(|(_, a), (_, b)| b.end <= a.end));

        active = expire_old_intervals(
            &vreg_range.1,
            &active,
            &mut free_registers,
            &vreg_to_memory_location,
        );

        assert!(active.len() <= abi.gprs.len());
        assert!(free_registers.len() <= abi.gprs.len());
        assert!(active.is_sorted_by(|(_, a), (_, b)| b.end <= a.end));

        // Already filled by pre-coloring?
        if vreg_to_memory_location.contains_key(&vreg_range.0) {
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

    vreg_to_memory_location
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

    assert!(new_active.len() <= active.len());
    assert!(new_active.is_sorted_by(|(_, a), (_, b)| b.end <= a.end));
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
    assert!(active.is_sorted_by(|(_, a), (_, b)| b.end <= a.end));
    match active.binary_search_by(|(_, range)| {
        let a = (range.end as u64) << 32 | (range.start as u64);
        let b = (item.1.end as u64) << 32 | (item.1.start as u64);
        b.cmp(&a)
    }) {
        Ok(_pos) => {
            panic!("element already present")
        }
        Err(pos) => active.insert(pos, item),
    }
    assert!(active.is_sorted_by(|(_, a), (_, b)| b.end <= a.end));
}
