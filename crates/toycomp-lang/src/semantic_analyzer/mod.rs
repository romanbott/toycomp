use std::{collections::HashMap, mem::uninitialized, process::id};

use crate::{
    AST,
    lang::{Expression, FunctionDefinition, Item, Operator, Statement, Type},
};

#[derive(Clone)]
struct FunctionSignature {
    args: Vec<Type>,
    return_type: Type,
}

#[derive(Clone)]
pub struct TypeChecker {
    function_table: HashMap<String, FunctionSignature>,
    symbol_table: HashMap<String, Type>,
}

#[derive(Debug)]
pub enum TypeChekingError {
    AssignmentTypeDonotMatch,
    UndeclaredIdent,
    MultipleDeclFunc,
    ReturnOutsideFunc,
    ReturnStmtDifferentFromDecl,
    VoidInsideExpression,
    OpBoolNumeric,
    FloatEqNotSupported,
    UndeclaredFunc,
    ArgsDontMatchSignature,
    ClauseNotBool,
}

impl TypeChecker {
    pub fn new() -> Self {
        TypeChecker {
            function_table: HashMap::new(),
            symbol_table: HashMap::new(),
        }
    }

    pub fn type_check(&mut self, ast: AST) -> Result<(), TypeChekingError> {
        match ast {
            AST::Program(items) => {
                for item in items {
                    match item {
                        Item::FunDef(function_definition) => {
                            self.type_check_func(function_definition)?
                        }

                        Item::Statement(statement) => {
                            if self.type_check_statement(statement)?.is_some() {
                                return Err(TypeChekingError::ReturnOutsideFunc);
                            }
                        }
                    }
                }
            }
            _ => unreachable!("Root node should be of variant Program."),
        };
        Ok(())
    }

    fn type_check_func(
        &mut self,
        function_definition: FunctionDefinition,
    ) -> Result<(), TypeChekingError> {
        if self
            .function_table
            .contains_key(&function_definition.ident.0)
        {
            return Err(TypeChekingError::MultipleDeclFunc);
        }

        let mut new_env = self.clone();

        for param in &function_definition.arguments {
            new_env
                .symbol_table
                .insert(param.ident.0.to_string(), param.typ.clone());
        }

        for stmt in function_definition.body {
            if let Some(ret_type) = new_env.type_check_statement(stmt)? {
                if ret_type != function_definition.return_type {
                    return Err(TypeChekingError::ReturnStmtDifferentFromDecl);
                }
            }
        }

        self.function_table.insert(
            function_definition.ident.0.to_string(),
            FunctionSignature {
                args: function_definition
                    .arguments
                    .iter()
                    .map(|a| a.typ.clone())
                    .collect(),
                return_type: function_definition.return_type,
            },
        );

        Ok(())
    }

    fn type_check_statement(
        &mut self,
        statement: Statement,
    ) -> Result<Option<Type>, TypeChekingError> {
        match statement {
            Statement::Declaration(identifier, decl_type, expression) => {
                if decl_type != self.type_check_expression(&expression)? {
                    return Err(TypeChekingError::AssignmentTypeDonotMatch);
                }
                self.symbol_table.insert(identifier.0.clone(), decl_type);
                Ok(None)
            }
            Statement::Assignment(identifier, expression) => {
                // discard variable does not need typing
                if identifier.0 == "_" {
                    return Ok(None);
                }
                if self.lookup(&identifier.0)? != self.type_check_expression(&expression)? {
                    return Err(TypeChekingError::AssignmentTypeDonotMatch);
                }
                Ok(None)
            }
            Statement::IfStatement(expression, statements, else_clause) => {
                if self.type_check_expression(&expression)?.is_bool() {
                    for stmt in statements {
                        self.type_check_statement(stmt)?;
                    }
                    if let Some(else_block) = else_clause {
                        for stmt in else_block.0 {
                            self.type_check_statement(stmt)?;
                        }
                    }
                    return Ok(None);
                }
                return Err(TypeChekingError::ClauseNotBool);
            }
            Statement::While(expression, statements) => {
                if self.type_check_expression(&expression)?.is_bool() {
                    for stmt in statements {
                        self.type_check_statement(stmt)?;
                    }
                    return Ok(None);
                }
                return Err(TypeChekingError::ClauseNotBool);
            }
            Statement::Return(expression) => Ok(Some(self.type_check_expression(&expression)?)),
        }
    }

    fn type_check_expression(&self, expression: &Expression) -> Result<Type, TypeChekingError> {
        match expression {
            Expression::Ident(identifier) => self.lookup(&identifier.0),
            Expression::Lit(literal) => Ok(literal.get_type()),
            Expression::FunCall(identifier, expressions) => {
                if let Some(signature) = self.function_table.get(&identifier.0) {
                    for (arg, param) in expressions.iter().zip(&signature.args) {
                        if &self.type_check_expression(arg)? != param {
                            return Err(TypeChekingError::ArgsDontMatchSignature);
                        }
                    }
                    return Ok(signature.return_type.clone());
                }
                Err(TypeChekingError::UndeclaredFunc)
            }
            Expression::Binary(op, left, right) => self.type_check_binary(op, left, right),
            Expression::Unary(op, exp) => self.type_check_unary(op, exp),
        }
    }

    fn type_check_unary(&self, op: &Operator, exp: &Expression) -> Result<Type, TypeChekingError> {
        match (op, self.type_check_expression(exp)?) {
            (Operator::Minus, Type::Int) => Ok(Type::Int),
            (Operator::Minus, Type::Float) => Ok(Type::Float),
            (Operator::Minus, _) => Err(TypeChekingError::OpBoolNumeric),
            (Operator::Not, Type::Bool) => Ok(Type::Bool),
            // TODO: Maybe change errors
            (Operator::Not, _) => Err(TypeChekingError::OpBoolNumeric),
            _ => unreachable!(),
        }
    }

    fn type_check_binary(
        &self,
        op: &Operator,
        left: &Expression,
        right: &Expression,
    ) -> Result<Type, TypeChekingError> {
        let left_type = self.type_check_expression(left)?;
        let right_type = self.type_check_expression(right)?;

        match (left_type, right_type) {
            (_, Type::Void) => return Err(TypeChekingError::VoidInsideExpression),
            (Type::Void, _) => return Err(TypeChekingError::VoidInsideExpression),
            (Type::Bool, Type::Bool) => match op {
                Operator::And | Operator::Or => Ok(Type::Bool),
                _ => return Err(TypeChekingError::OpBoolNumeric),
            },
            (Type::Bool, _) => return Err(TypeChekingError::OpBoolNumeric),
            (_, Type::Bool) => return Err(TypeChekingError::OpBoolNumeric),
            (Type::Int, Type::Int) => match op {
                Operator::Times
                | Operator::Div
                | Operator::Plus
                | Operator::Minus
                | Operator::Mod => Ok(Type::Int),
                Operator::Equal
                | Operator::NotEqual
                | Operator::Lesser
                | Operator::LTE
                | Operator::Greater
                | Operator::GTE => Ok(Type::Bool),
                _ => unreachable!("All cases should be handled by now."),
            },
            (_, _) => match op {
                Operator::Times | Operator::Div | Operator::Plus | Operator::Minus => {
                    Ok(Type::Float)
                }
                Operator::Lesser | Operator::LTE | Operator::Greater | Operator::GTE => {
                    Ok(Type::Bool)
                }
                Operator::Equal | Operator::NotEqual => Err(TypeChekingError::FloatEqNotSupported),
                _ => unreachable!("All cases should be handled by now."),
            },
        }
    }

    fn lookup(&self, ident: &str) -> Result<Type, TypeChekingError> {
        self.symbol_table
            .get(ident)
            .ok_or(TypeChekingError::UndeclaredIdent)
            .cloned()
    }
}
