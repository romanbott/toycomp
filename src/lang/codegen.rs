use crate::lang::ast::{AST, Expression, Literal};
use std::io::{self, Write};
pub struct Codegen {
    temp_counter: usize,
    label_counter: usize,
}

impl Codegen {
    pub fn new() -> Self {
        Codegen {
            temp_counter: 0,
            label_counter: 0,
        }
    }
    fn make_temp(&mut self) -> String {
        self.temp_counter += 1;
        format!("_t{}", self.temp_counter)
    }
    fn make_label(&mut self, base: Option<&str>) -> String {
        self.label_counter += 1;
        let base_str = base.unwrap_or("L");
        format!("{}_{}", base_str, self.label_counter)
    }
    fn emit_var<W: Write>(&self, out: &mut W, name: &str) -> io::Result<()> {
        writeln!(out, "VAR {}", name)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
}
