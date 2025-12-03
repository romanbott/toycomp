use crate::lang::ast::{AST, ElseClause, Expression, Item, Literal, Operator, Statement};
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
            // TODO:
            // handle std functions:
            // - print
            // - input
            // - pixel
            // - mod
            // - time
            // - key
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

    fn gen_stmt<W: Write>(&mut self, stmt: Statement, out: &mut W) -> io::Result<()> {
        match stmt {
            Statement::Declaration(identifier, _, expression) => {
                self.emit_var(out, &identifier.0)?;
                self.gen_stmt(Statement::Assignment(identifier, expression), out)?
            }
            Statement::Assignment(identifier, expression) => {
                let src = self.gen_expr(&expression, out)?;
                writeln!(out, "ASSIGN {} {}", src, identifier.0)?;
            }
            Statement::IfStatement(expression, statements, else_clause) => {
                let cond = self.gen_expr(&expression, out)?;
                let label_then = self.make_label(Some("THEN"));
                let label_end = self.make_label(Some("ENDIF"));

                writeln!(out, "IF {} GOTO {}", cond, label_then)?;

                if let Some(ElseClause(statements)) = else_clause {
                    for stmt in statements {
                        self.gen_stmt(stmt, out)?;
                    }
                }

                writeln!(out, "GOTO {}", label_end)?;
                writeln!(out, "LABEL {}", label_then)?;
                for stmt in statements {
                    self.gen_stmt(stmt, out)?;
                }
                writeln!(out, "LABEL {}", label_end)?;
            }
            Statement::While(expression, statements) => {
                let start = self.make_label(Some("WHILE_START"));
                let end = self.make_label(Some("WHILE_END"));

                writeln!(out, "LABEL {}", start)?;
                let cond = self.gen_expr(&expression, out)?;
                writeln!(out, "IFFALSE {} GOTO {}", cond, end)?;
                for stmt in statements {
                    self.gen_stmt(stmt, out)?;
                }
                writeln!(out, "GOTO {}", start)?;
                writeln!(out, "LABEL {}", end)?;
            }
            Statement::Return(expression) => {
                let val = self.gen_expr(&expression, out)?;
                writeln!(out, "RETURN {}", val)?;
            }
        }
        Ok(())
    }

    fn gen_item<W: Write>(&mut self, item: Item, out: &mut W) -> io::Result<()> {
        match item {
            Item::FunDef(fun) => {
                writeln!(out, "LABEL {}", fun.ident.0)?;

                for stmt in fun.body {
                    self.gen_stmt(stmt, out)?;
                }

                writeln!(out, "RETURN 0")?;
            }
            Item::Statement(statement) => self.gen_stmt(statement, out)?,
        }
        Ok(())
    }

    fn gen_program<W: Write>(&mut self, program: AST, out: &mut W) -> io::Result<()> {
        match program {
            AST::Program(items) => {
                for item in items {
                    self.gen_item(item, out)?
                }
            }
            _ => {
                panic!("Root node should be a Program.")
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::{
        ast::{Identifier, Operator, Type},
        ast_builder::ASTBuilder,
        parser::Parser,
    };

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

    #[test]
    fn if_stmt_gen() {
        let stmt = Statement::IfStatement(
            1.into(),
            vec![Statement::Declaration("x".into(), Type::Int, 1.into())],
            None,
        );

        let mut cg = Codegen::new();

        let mut buffer: Vec<u8> = Vec::new();
        _ = cg.gen_stmt(stmt, &mut buffer);

        let result_string = String::from_utf8(buffer).unwrap();

        assert_eq!(
            "VAR _t1\nASSIGN 1 _t1\nIF _t1 GOTO THEN_1\nGOTO ENDIF_2\nLABEL THEN_1\nVAR x\nVAR _t2\nASSIGN 1 _t2\nASSIGN _t2 x\nLABEL ENDIF_2\n",
            result_string
        )
    }
}
