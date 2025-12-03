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
#[cfg(test)]
mod tests {

    use super::*;
}
