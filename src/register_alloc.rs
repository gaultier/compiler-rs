use std::collections::BTreeMap;

use crate::{
    asm::Abi,
    ir::{Lifetimes, VirtualRegister},
};

#[derive(Copy, Clone)]
pub struct Register(u8);

pub enum MemoryLocation {
    Register(Register),
    Stack(u32), // Stack offset.
}

pub type RegAlloc = BTreeMap<VirtualRegister, MemoryLocation>;

// TODO: Constraints.
pub fn regalloc(lifetimes: &Lifetimes, abi: &Abi) -> RegAlloc {
    let mut res = RegAlloc::new();

    // TODO: Linear register allocator.

    res
}
