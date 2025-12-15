use std::collections::{BTreeMap, BTreeSet};

use log::trace;
use serde::Serialize;

use crate::{
    asm::{Abi, Register},
    ir::{LiveRange, LiveRanges, VirtualRegister},
};

#[derive(Serialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum MemoryLocation {
    Register(Register),
    Stack(isize), // Stack offset.
}

pub enum Action {
    // Spill a register to a stack slot.
    Spill(usize, Register),
    // Reload a register from a stack slot.
    Reload(Register, usize),
}

pub type RegisterMapping = BTreeMap<VirtualRegister, MemoryLocation>;

pub(crate) fn regalloc(live_ranges: &LiveRanges, abi: &Abi) -> (RegisterMapping, isize) {
    let mut vreg_to_memory_location = RegisterMapping::new();
    let mut stack_offset = 0isize; // Grows downward.

    let mut free_registers = BTreeSet::<Register>::new();
    for register in &abi.gprs {
        free_registers.insert(*register);
    }

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

    for (vreg, live_range) in &live_ranges_start_asc {
        assert!(free_registers.len() <= abi.gprs.len());
        assert!(active.len() <= abi.gprs.len());
        assert!(active.is_sorted_by(|(_, a), (_, b)| b.end <= a.end));

        active = expire_old_intervals(
            live_range,
            &active,
            &mut free_registers,
            &vreg_to_memory_location,
        );

        assert!(active.len() <= abi.gprs.len());
        assert!(free_registers.len() <= abi.gprs.len());
        assert!(active.is_sorted_by(|(_, a), (_, b)| b.end <= a.end));

        if active.len() == abi.gprs.len() {
            spill_at_interval(
                vreg,
                live_range,
                &mut active,
                &mut vreg_to_memory_location,
                &mut stack_offset,
            );
        } else {
            // TODO: We could have a heuristic here instead of just 'the first free register'.
            let free_register = free_registers.pop_first().unwrap();
            vreg_to_memory_location.insert(*vreg, MemoryLocation::Register(free_register));
            insert_sorted(&mut active, (*vreg, *live_range));

            trace!(
                "regalloc: msg='alloc preg for vreg' vreg={} live_range={} preg={}",
                vreg, live_range, free_register
            );
        }
    }

    (vreg_to_memory_location, stack_offset)
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
        trace!(
            "regalloc: msg='expire old intervals' live_range_at={} vreg={} live_range={}",
            live_range_at, vreg, live_range
        );

        // TODO: Could probably be optimized?
        new_active = new_active
            .extract_if(.., |&mut e| &e.1 == live_range)
            .collect();

        if let MemoryLocation::Register(preg) = vreg_to_memory_location[vreg] {
            free_registers.insert(preg);
            trace!(
                "regalloc: msg='expire old intervals' live_range_at={} vreg={} live_range={} preg={}",
                live_range_at, vreg, live_range, preg,
            );
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
//
// > Our algorithm spills the interval that ends last, furthest away
// > from the current point. We can find this interval quickly because active is sorted
// > by increasing end point: the interval to be spilled is either the new interval or
// > the last interval in active, whichever ends later. In straight-line code, and when
// > each live interval consists of exactly one definition followed by one use, this heuristic
// > produces code with the minimal possible number of spilled live ranges [...].
fn spill_at_interval(
    vreg_current: &VirtualRegister,
    live_range_current: &LiveRange,
    active: &mut Vec<(VirtualRegister, LiveRange)>,
    vreg_to_memory_location: &mut RegisterMapping,
    stack_offset: &mut isize,
) {
    let (vreg_last, live_range_last) = *active.last().unwrap();
    if live_range_last.end > live_range_current.end {
        // register[i] ← register[spill]
        let memory_location_last = *vreg_to_memory_location.get(&vreg_last).unwrap();
        vreg_to_memory_location.insert(*vreg_current, memory_location_last);

        // location[spill] ← new stack location
        *stack_offset -= 8; // TODO: correct size.
        vreg_to_memory_location.insert(vreg_last, MemoryLocation::Stack(*stack_offset));

        // remove spill from active
        let pos_remove = active.iter().position(|x| x.0 == vreg_last).unwrap();
        active.remove(pos_remove);

        // add i to active, sorted by increasing end point
        insert_sorted(active, (*vreg_current, *live_range_current));

        trace!(
            "regalloc: msg='spill last interval in active' vreg_last={} vreg_current={} memory_location={:#?} stack_offset={}",
            vreg_last, vreg_current, memory_location_last, stack_offset
        );
    } else {
        *stack_offset -= 8; // TODO: correct size.
        vreg_to_memory_location.insert(*vreg_current, MemoryLocation::Stack(*stack_offset));

        trace!(
            "regalloc: msg='spill new interval' vreg_current={} stack_offset={}",
            vreg_current, stack_offset
        );
    }
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
