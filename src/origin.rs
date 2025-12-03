use serde::{Deserialize, Serialize};
//use std::rc::Rc;

#[derive(PartialEq, Eq, Debug, Serialize, Deserialize, Copy, Clone)]
pub struct Origin {
    pub line: u32,
    pub column: u32,
    pub offset: u32,
    //    pub file: Rc<Vec<u8>>,
}

impl Origin {
    pub(crate) fn new(line: u32, column: u32, offset: u32 /*, file: Rc<Vec<u8>>*/) -> Self {
        Self {
            line,
            column,
            offset,
            //file,
        }
    }
}
