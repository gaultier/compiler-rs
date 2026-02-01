use std::collections::HashMap;

use crate::ir;

pub(crate) struct ControlFlowGraph {
    blocks: Vec<ControlFlowBlock>,
    name_to_block: HashMap<String, BlockId>,
}

pub(crate) struct ControlFlowBlock {
    // IR indices inside the function body.
    start: usize,
    end: usize,
    name: String,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct BlockId(usize);

impl ControlFlowGraph {
    pub(crate) fn new() -> Self {
        Self {
            blocks: Vec::new(),
            name_to_block: HashMap::new(),
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
                    let block_id = self.name_to_block.get(name).unwrap();
                }

                ir::InstructionKind::LabelDef(name) => {
                    self.new_block(ControlFlowBlock {
                        start: i,
                        end: i,
                        name: name.to_owned(),
                    });
                }
            }
        }
    }
}
