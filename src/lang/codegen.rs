use crate::lang::ast::{AST, Expression, Literal, Operator};
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

    fn gen_expr<W: Write>(&mut self, expr: &Expression, out: &mut W) -> io::Result<String> {
        match expr {
            Expression::Lit(value) => {
                let buf = format!("{}", value);
                let t = self.make_temp();
                self.emit_var(out, &t)?;
                writeln!(out, "ASSIGN {} {}", buf, t)?;
                Ok(t)
            }
            // TODO: revisar
            Expression::Ident(ident) => Ok(ident.0.to_string()),

            Expression::Binary(o, l, r) => {
                let a = self.gen_expr(l, out)?;
                let b = self.gen_expr(r, out)?;

                let dest = self.make_temp();
                self.emit_var(out, &dest)?;

                writeln!(out, "{} {} {} {}", o, a, b, dest)?;

                Ok(dest)
            }

            Expression::Unary(Operator::Not, l) => {
                let a = self.gen_expr(l, out)?;
                let dest = self.make_temp();
                self.emit_var(out, &dest)?;

                writeln!(out, "NOT {} {}", a, dest)?;

                Ok(dest)
            }

            Expression::Unary(Operator::Minus, l) => {
                let a = self.gen_expr(l, out)?;
                let dest = self.make_temp();
                self.emit_var(out, &dest)?;
                writeln!(out, "SUB 0 {} {}", a, dest)?;
                Ok(dest)
            }
            Expression::FunCall(ident, args) => {
                let ret = self.make_temp();
                self.emit_var(out, &ret)?;

                for expr in args {
                    let a = self.gen_expr(expr, out)?;
                    writeln!(out, "PARAM {}", a)?;
                }

                writeln!(out, "GOSUB {} {}", ident.0, ret)?;

                Ok(ret)
            }
            _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::ast::{Identifier, Operator};

    use super::*;

    #[test]
    fn simple_expression_gen() {
        let expr = Expression::Binary(Operator::Plus, 1.into(), 2.into());

        let mut cg = Codegen::new();

        let mut buffer: Vec<u8> = Vec::new();
        _ = cg.gen_expr(&expr, &mut buffer);

        let result_string = String::from_utf8(buffer);

        assert_eq!(
            "VAR _t1\nASSIGN 1 _t1\nVAR _t2\nASSIGN 2 _t2\nVAR _t3\nADD _t1 _t2 _t3\n",
            result_string.unwrap().as_str()
        )
    }

    #[test]
    fn call_expr_gen() {
        let expr = Expression::FunCall("f".into(), vec![1.into(), 2.into()]);

        let mut cg = Codegen::new();

        let mut buffer: Vec<u8> = Vec::new();
        _ = cg.gen_expr(&expr, &mut buffer);

        let result_string = String::from_utf8(buffer);

        assert_eq!(
            "VAR _t1\nVAR _t2\nASSIGN 1 _t2\nPARAM _t2\nVAR _t3\nASSIGN 2 _t3\nPARAM _t3\nGOSUB f _t1\n",
            result_string.unwrap().as_str()
        )
    }
        assert_eq!(
            "VAR _t1\nASSIGN 1 _t1\nVAR _t2\nASSIGN 2 _t2\nVAR _t3\nADD _t1 _t2 _t3\n",
            result_string.unwrap().as_str()
        )
    }
}
