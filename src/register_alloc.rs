use std::collections::{BTreeMap, BTreeSet};

use crate::{
    asm::Abi,
    ir::{Lifetime, Lifetimes, VirtualRegister},
};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Register(pub u8);

pub enum MemoryLocation {
    Register(Register),
    Stack(u32), // Stack offset.
}

pub type RegAlloc = BTreeMap<VirtualRegister, MemoryLocation>;

impl Register {
    pub fn as_u8(&self) -> u8 {
        self.0
    }
}

// TODO: Constraints.
pub fn regalloc(lifetimes: &Lifetimes, abi: &Abi) -> RegAlloc {
    let mut res = RegAlloc::new();

    let mut free_registers = BTreeSet::<Register>::new();
    for register in &abi.gprs {
        free_registers.insert(*register);
    }

    let mut active = BTreeSet::<usize>::new();

    let mut lifetimes_start_asc = lifetimes.iter().collect::<Vec<_>>();
    lifetimes_start_asc.sort_by(|(_, a), (_, b)| a.start.cmp(&b.start));

    let mut lifetimes_end_desc: Vec<_> = lifetimes_start_asc.clone();
    lifetimes_end_desc.sort_by(|(_, a), (_, b)| b.end.cmp(&a.end));

    for (i, (vreg, _lifetime)) in lifetimes_start_asc.iter().enumerate() {
        expire_old_intervals(
            i,
            &lifetimes_start_asc,
            &lifetimes_end_desc,
            &mut active,
            &mut free_registers,
            &res,
        );

        if active.len() == abi.gprs.len() {
            spill_at_interval(i, &lifetimes_end_desc, &mut active);
        } else {
            let free_register = free_registers.pop_first().unwrap();
            res.insert(**vreg, MemoryLocation::Register(free_register));
            active.insert(i);
        }
    }

    // TODO: Linear register allocator.

    res
}

fn expire_old_intervals(
    pos: usize,
    lifetimes_start_asc: &[(&VirtualRegister, &Lifetime)],
    lifetimes_end_desc: &[(&VirtualRegister, &Lifetime)],
    active: &mut BTreeSet<usize>,
    free_registers: &mut BTreeSet<Register>,
    regalloc: &RegAlloc,
) {
    assert_eq!(lifetimes_start_asc.len(), lifetimes_end_desc.len());

    for (j, (vreg, lifetime)) in lifetimes_end_desc.iter().enumerate() {
        let end = lifetime.end;
        let start = lifetimes_start_asc[pos].1.start;
        if end >= start {
            return;
        }
        active.remove(&j);
        let register = match regalloc[vreg] {
            MemoryLocation::Register(reg) => reg,
            _ => panic!("should be assigned a register"),
        };
        free_registers.insert(register);
    }
}

fn spill_at_interval(
    pos: usize,
    lifetimes_end_desc: &[(&VirtualRegister, &Lifetime)],
    active: &mut BTreeSet<usize>,
) {
    let spill_interval = *active.last().unwrap();
    if lifetimes_end_desc[spill_interval].1.end > lifetimes_end_desc[pos].1.end {
        todo!()
    } else {
        todo!()
    }
}
