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
    current_block: Option<BlockId>,
}

pub(crate) struct ControlFlowBlock {
    // IR indices inside the function body.
    start: usize,
    end: usize,
    name: String,
    children: HashSet<BlockId>,
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
            current_block: None,
        }
    }

    fn new_block(&mut self, block: ControlFlowBlock) -> BlockId {
        let id = BlockId(self.blocks.len());
        assert_eq!(self.name_to_block.insert(block.name.to_owned(), id), None);
        self.blocks.push(block);

        id
    }

    pub(crate) fn compute(&mut self, irs: &[ir::Instruction]) {
        for (i, ir) in irs.iter().enumerate() {
            match &ir.kind {
                ir::InstructionKind::IAdd(_, _)
                | ir::InstructionKind::IMultiply(_, _)
                | ir::InstructionKind::IDivide(_, _)
                | ir::InstructionKind::ICmp(_, _)
                | ir::InstructionKind::Set(_)
                | ir::InstructionKind::FnCall(_, _) => {}

                ir::InstructionKind::JumpIfFalse(name, _) | ir::InstructionKind::Jump(name) => {
                    // FIXME: In case of forward jump, the block does not exist yet.
                    let target_block_id = *self.name_to_block.get(name).unwrap();

                    let current_block_id = self.current_block.unwrap();
                    let current_block = &mut self.blocks[current_block_id];
                    current_block.children.insert(target_block_id);
                }

                ir::InstructionKind::LabelDef(name) => {
                    self.new_block(ControlFlowBlock {
                        start: i,
                        end: i,
                        name: name.to_owned(),
                        children: HashSet::new(),
                    });
                }
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
        writeln!(
            f,
            "{}: name={} start={} end={}\n",
            id.0, block.name, block.start, block.end
        )?;

        for child in &block.children {
            writeln!(f, "{} -> {}", id.0, child.0)?;
        }

        for child in &block.children {
            Self::print(f, *child, blocks, visited)?;
        }

        Ok(())
    }
}
