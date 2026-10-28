use crate::lang::ast::{
    AST, ElseClause, Expression, Identifier, Item, Literal, Operator, Statement,
};
use std::{
    collections::{HashMap, HashSet},
    io::{self, Write},
};

pub struct Codegen {
    temp_counter: usize,
    label_counter: usize,
}

const BUILT_INS: [&str; 7] = ["print", "pixel", "input", "time", "mod", "pow", "poll_key"];

fn is_builtin(ident: &Identifier) -> bool {
    BUILT_INS.iter().any(|&target| ident.0 == target)
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

    fn emit_local_var<W: Write>(&self, out: &mut W, name: &str, env: &str) -> io::Result<()> {
        writeln!(out, "VAR {}_{}", env, name)
    }

    fn gen_expr<W: Write>(
        &mut self,
        expr: &Expression,
        out: &mut W,
        env: Option<&HashMap<String, String>>,
    ) -> io::Result<String> {
        match expr {
            Expression::Lit(value) => {
                let buf = format!("{}", value);
                let t = self.make_temp();
                self.emit_var(out, &t)?;
                writeln!(out, "ASSIGN {} {}", buf, t)?;
                Ok(t)
            }
            // TODO: revisar
            Expression::Ident(identifier) => {
                let target = env
                    .map(|env| env.get(&identifier.0))
                    .flatten()
                    .unwrap_or(&identifier.0);

                Ok(target.clone())
            }

            Expression::Binary(o, l, r) => {
                let a = self.gen_expr(l, out, env)?;
                let b = self.gen_expr(r, out, env)?;

                let dest = self.make_temp();
                self.emit_var(out, &dest)?;

                writeln!(out, "{} {} {} {}", o, a, b, dest)?;

                Ok(dest)
            }

            Expression::Unary(Operator::Not, l) => {
                let a = self.gen_expr(l, out, env)?;
                let dest = self.make_temp();
                self.emit_var(out, &dest)?;

                writeln!(out, "NOT {} {}", a, dest)?;

                Ok(dest)
            }

            Expression::Unary(Operator::Minus, l) => {
                let a = self.gen_expr(l, out, env)?;
                let dest = self.make_temp();
                self.emit_var(out, &dest)?;
                writeln!(out, "SUB 0 {} {}", a, dest)?;
                Ok(dest)
            }
            Expression::FunCall(ident, args) => {
                if is_builtin(ident) {
                    return self.gen_builtin(ident, args, out, env);
                }

                let ret = self.make_temp();
                self.emit_var(out, &ret)?;

                for expr in args {
                    let a = self.gen_expr(expr, out, env)?;
                    writeln!(out, "PARAM {}", a)?;
                }

                writeln!(out, "GOSUB {}", ident.0)?;

                Ok("_GLOBAL_RETURN".to_string())
            }
            _ => unimplemented!(),
        }
    }

    fn gen_stmt<W: Write>(
        &mut self,
        stmt: Statement,
        out: &mut W,
        env: Option<&HashMap<String, String>>,
    ) -> io::Result<()> {
        match stmt {
            Statement::Declaration(identifier, _, expression) => {
                // TODO: handle collisions
                self.emit_var(out, &identifier.0)?;
                self.gen_stmt(Statement::Assignment(identifier, expression), out, env)?
            }
            Statement::Assignment(identifier, expression) => {
                let src = self.gen_expr(&expression, out, env)?;
                if &identifier.0 != "_" {
                    let target = env
                        .map(|env| env.get(&identifier.0))
                        .flatten()
                        .unwrap_or(&identifier.0);
                    writeln!(out, "ASSIGN {} {}", src, target)?;
                }
            }
            Statement::IfStatement(expression, statements, else_clause) => {
                let cond = self.gen_expr(&expression, out, env)?;
                let label_then = self.make_label(Some("THEN"));
                let label_end = self.make_label(Some("ENDIF"));

                writeln!(out, "IF {} GOTO {}", cond, label_then)?;

                if let Some(ElseClause(statements)) = else_clause {
                    for stmt in statements {
                        self.gen_stmt(stmt, out, env)?;
                    }
                }

                writeln!(out, "GOTO {}", label_end)?;
                writeln!(out, "LABEL {}", label_then)?;
                for stmt in statements {
                    self.gen_stmt(stmt, out, env)?;
                }
                writeln!(out, "LABEL {}", label_end)?;
            }
            Statement::While(expression, statements) => {
                let start = self.make_label(Some("WHILE_START"));
                let end = self.make_label(Some("WHILE_END"));

                writeln!(out, "LABEL {}", start)?;
                let cond = self.gen_expr(&expression, out, env)?;
                writeln!(out, "IFFALSE {} GOTO {}", cond, end)?;
                for stmt in statements {
                    self.gen_stmt(stmt, out, env)?;
                }
                writeln!(out, "GOTO {}", start)?;
                writeln!(out, "LABEL {}", end)?;
            }
            Statement::Return(expression) => {
                let val = self.gen_expr(&expression, out, env)?;
                writeln!(out, "ASSIGN {} _GLOBAL_RETURN", val)?;
                writeln!(out, "RETURN")?;
            }
        }
        Ok(())
    }

    fn gen_item<W: Write>(&mut self, item: Item, out: &mut W) -> io::Result<()> {
        match item {
            Item::FunDef(fun) => {
                // let fun_label = self.make_label(Some(&fun.ident.0));

                writeln!(out, "GOTO END_{}", fun.ident.0)?;
                writeln!(out, "LABEL {}", fun.ident.0)?;

                let mut local_env = HashMap::new();
                for arg in fun.arguments.iter().rev() {
                    // TODO: fix possible collisions
                    let new_ident = format!("_{}_{}", &fun.ident.0, &arg.ident.0);
                    self.emit_var(out, &new_ident)?;
                    writeln!(out, "PARAM_GET {}", &new_ident)?;
                    local_env.insert(arg.ident.0.clone(), new_ident);
                }

                for stmt in fun.body {
                    self.gen_stmt(stmt, out, Some(&local_env))?;
                }
                writeln!(out, "LABEL END_{}", fun.ident.0)?;
            }
            Item::Statement(statement) => self.gen_stmt(statement, out, None)?,
        }
        Ok(())
    }

    pub fn gen_program<W: Write>(&mut self, program: AST, out: &mut W) -> io::Result<()> {
        match program {
            AST::Program(items) => {
                // Declares global variable for builin returns
                writeln!(out, "VAR _GLOBAL_RETURN")?;
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

    fn gen_builtin<W: Write>(
        &mut self,
        ident: &Identifier,
        args: &[Expression],
        out: &mut W,
        env: Option<&HashMap<String, String>>,
    ) -> io::Result<String> {
        match (ident.0.as_str(), args) {
            ("print", [expression]) => {
                let t = self.gen_expr(expression, out, env)?;
                writeln!(out, "PRINT {}", t)?;
            }
            ("pixel", [e1, e2, e3]) => {
                let a = self.gen_expr(e1, out, env)?;
                let b = self.gen_expr(e2, out, env)?;
                let c = self.gen_expr(e3, out, env)?;
                writeln!(out, "PIXEL {} {} {}", a, b, c)?;
            }
            ("input", []) => {
                let ret = self.make_temp();
                self.emit_var(out, &ret)?;
                writeln!(out, "INPUT {}", ret)?;
                return Ok(ret);
            }
            ("time", []) => {
                let ret = self.make_temp();
                self.emit_var(out, &ret)?;
                writeln!(out, "TIME {}", ret)?;
                return Ok(ret);
            }
            ("mod", [e1, e2]) => {
                let ret = self.make_temp();
                self.emit_var(out, &ret)?;
                let a = self.gen_expr(e1, out, env)?;
                let b = self.gen_expr(e2, out, env)?;
                writeln!(out, "MOD {} {} {}", a, b, ret)?;
                return Ok(ret);
            }
            ("pow", [e1, e2]) => {
                let ret = self.make_temp();
                self.emit_var(out, &ret)?;
                let a = self.gen_expr(e1, out, env)?;
                let b = self.gen_expr(e2, out, env)?;
                writeln!(out, "POW {} {} {}", a, b, ret)?;
                return Ok(ret);
            }
            ("poll_key", [e]) => {
                let ret = self.make_temp();
                self.emit_var(out, &ret)?;
                let key_code = self.gen_expr(e, out, env)?;
                writeln!(out, "KEY {} {}", key_code, ret)?;
                return Ok(ret);
            }
            _ => {}
        }
        Ok("_GLOBAL_RETURN".to_string())
    }
}
