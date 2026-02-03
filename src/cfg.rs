use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Index, IndexMut},
};

use crate::ir;

pub(crate) struct ControlFlowGraph {
    blocks: Vec<ControlFlowBlock>,
    name_to_block: HashMap<String, BlockId>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub(crate) struct Jump {
    target: BlockId,
    ir_idx: usize,
}

pub(crate) struct ControlFlowBlock {
    // IR index inside the function body.
    start: usize,
    name: String,
    children: HashSet<Jump>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub(crate) struct BlockId(usize);

impl Index<BlockId> for [ControlFlowBlock] {
    type Output = ControlFlowBlock;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self[index.0]
    }
}

impl IndexMut<BlockId> for [ControlFlowBlock] {
    fn index_mut(&mut self, index: BlockId) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl IndexMut<BlockId> for Vec<ControlFlowBlock> {
    fn index_mut(&mut self, index: BlockId) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl Index<BlockId> for Vec<ControlFlowBlock> {
    type Output = ControlFlowBlock;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self[index.0]
    }
}

impl ControlFlowGraph {
    pub(crate) fn new() -> Self {
        Self {
            blocks: Vec::new(),
            name_to_block: HashMap::new(),
        }
    }

    fn new_block(&mut self, block: ControlFlowBlock) {
        let id = BlockId(self.blocks.len());
        if !block.name.is_empty() {
            assert_eq!(self.name_to_block.insert(block.name.to_owned(), id), None);
        }
        self.blocks.push(block);
    }

    // TODO: Patch the `end` field.
    fn collect_all_blocks(&mut self, irs: &[ir::Instruction]) {
        if irs.is_empty() {
            return;
        }

        self.new_block(ControlFlowBlock {
            start: 0,
            name: String::from(""),
            children: HashSet::new(),
        });

        for (i, ir) in irs.iter().enumerate() {
            match &ir.kind {
                ir::InstructionKind::LabelDef(name) => {
                    self.new_block(ControlFlowBlock {
                        start: i,
                        name: name.to_owned(),
                        children: HashSet::new(),
                    });
                }
                ir::InstructionKind::JumpIfFalse(_name, _) => {
                    self.new_block(ControlFlowBlock {
                        start: i + 1,
                        name: String::new(), // TODO: Should we invent a name here e.g. 'if-then`?
                        children: HashSet::new(),
                    });
                }
                _ => {}
            }
        }
    }

    pub(crate) fn compute(&mut self, irs: &[ir::Instruction]) {
        self.collect_all_blocks(irs);
        let mut current_block_id = 0;

        for (i, ir) in irs.iter().enumerate() {
            dbg!(i, current_block_id);
            match &ir.kind {
                ir::InstructionKind::JumpIfFalse(name, _) => {
                    let target_block_id = *self.name_to_block.get(name).unwrap();
                    dbg!(i, target_block_id, name);
                    let fallthrough_block_id = BlockId(current_block_id + 1);

                    let current_block = &mut self.blocks[current_block_id];
                    current_block.children.insert(Jump {
                        target: target_block_id,
                        ir_idx: i,
                    });
                    current_block.children.insert(Jump {
                        target: fallthrough_block_id,
                        ir_idx: i,
                    });

                    current_block_id += 1;
                }
                ir::InstructionKind::Jump(name) => {
                    let target_block_id = *self.name_to_block.get(name).unwrap();
                    dbg!(i, target_block_id, name);

                    let current_block = &mut self.blocks[current_block_id];
                    current_block.children.insert(Jump {
                        target: target_block_id,
                        ir_idx: i,
                    });
                }
                &ir::InstructionKind::LabelDef(_) => {
                    current_block_id += 1;
                }

                _ => {}
            }
        }
    }
}

impl Display for ControlFlowGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut visited: HashSet<BlockId> = HashSet::new();

        for i in 0..self.blocks.len() {
            ControlFlowBlock::print(f, BlockId(i), self.blocks.as_slice(), &mut visited)?;
        }

        Ok(())
    }
}

impl ControlFlowBlock {
    fn print(
        f: &mut std::fmt::Formatter<'_>,
        id: BlockId,
        blocks: &[ControlFlowBlock],
        visited: &mut HashSet<BlockId>,
    ) -> std::fmt::Result {
        if !visited.insert(id) {
            return Ok(());
        }

        let block = &blocks[id];
        writeln!(f, "{}: name={} start={}", id.0, block.name, block.start)?;

        for child in &block.children {
            writeln!(f, "{} -> {} | {}", id.0, child.target.0, child.ir_idx)?;
        }

        for child in &block.children {
            Self::print(f, child.target, blocks, visited)?;
        }

        Ok(())
    }
}
