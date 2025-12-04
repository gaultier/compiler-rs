use std::{fmt, io::Write};

use miniserde::Serialize;
//use std::rc::Rc;

#[derive(PartialEq, Eq, Debug, Serialize, Copy, Clone)]
pub struct Origin {
    pub line: u32,
    pub column: u32,
    pub offset: u32,
    pub len: u32,
    //    pub file: Rc<Vec<u8>>,
}

impl Origin {
    pub(crate) fn new(
        line: u32,
        column: u32,
        offset: u32,
        len: u32, /*, file: Rc<Vec<u8>>*/
    ) -> Self {
        Self {
            line,
            column,
            offset,
            len,
            //file,
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        // TODO: file name.
        write!(w, "{}:{}:{}", self.line, self.column, self.offset)?;

        Ok(())
    }
}
