use std::collections::BTreeMap;

use crate::ir::{Lifetimes, VirtualRegister};

pub struct Register(u8);

pub enum MemoryLocation {
    Register(Register),
    Stack(u32), // Stack offset.
}

pub type RegAlloc = BTreeMap<VirtualRegister, MemoryLocation>;

pub fn regalloc(lifetimes: &Lifetimes) -> RegAlloc {
    let mut res = RegAlloc::new();

    // TODO

    res
}
