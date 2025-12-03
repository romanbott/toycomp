use std::str::FromStr;

use crate::{
    lexer::Token,
    static_analyzer::{Production, TreeBuilder, TreeBuilderError},
};

#[derive(Default)]
struct ASTBuilder {
    stack: Vec<AST>,
}

impl ASTBuilder {
    fn new() -> Self {
        ASTBuilder { stack: Vec::new() }
    }
    fn peak3(&self) -> Option<(&AST, &AST, &AST)> {
        self.stack[self.stack.len() - 3..]
            .try_into()
            .ok()
            .map(|arr: &[AST; 3]| (&arr[0], &arr[1], &arr[2]))
    }

    fn peak2(&self) -> Option<(&AST, &AST)> {
        self.stack[self.stack.len() - 2..]
            .try_into()
            .ok()
            .map(|arr: &[AST; 2]| (&arr[0], &arr[1]))
    }

    fn get2(&mut self) -> Option<(AST, AST)> {
        let last = self.stack.pop()?;
        self.stack.pop().map(|s| (s, last))
    }

    fn get3(&mut self) -> Option<(AST, AST, AST)> {
        let (s, l) = self.get2()?;
        self.stack.pop().map(|t| (t, s, l))
    }

    fn discard_last_n(&mut self, to_discard: usize) -> Result<(), ()> {
        let len = self.stack.len();

        if len < to_discard {
            return Err(());
        }

        self.stack.truncate(len - to_discard);

        Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub enum Item {
    FunDef(FunctionDefinition),
    Statement(Statement),
}

#[derive(Debug, PartialEq)]
pub struct FunctionDefinition {
    ident: Identifier,
    return_type: Type,
    arguments: Vec<Param>,
    body: Vec<Statement>,
}

#[derive(Debug, PartialEq)]
pub enum Literal {
    Int(i64),
    Bool(bool),
    Float(f64),
}

impl TryFrom<&Token> for Literal {
    type Error = TreeBuilderError;

    fn try_from(token: &Token) -> Result<Self, Self::Error> {
        let op = match (token.tag.as_str(), token.value.as_str()) {
            ("INTEGER_LITERAL", s) => s.parse().ok().map(Literal::Int),
            ("BOOLEAN_LITERAL", s) => s.parse().ok().map(Literal::Bool),
            ("FLOAT_LITERAL", s) => s.parse().ok().map(Literal::Float),
            _ => {
                return Err(TreeBuilderError::ShiftError(format!(
                    "Error while shifting litera: found: {:?}",
                    token
                )));
            }
        };
        op.ok_or(TreeBuilderError::ShiftError(format!(
            "Error while parsing literal, found: {:?}",
            token,
        )))
    }
}

#[derive(Debug, PartialEq)]
pub struct Param {
    ident: Identifier,
    typ: Type,
}

#[derive(Debug, PartialEq)]
pub struct ElseClause {
    block: Vec<Statement>,
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Declaration(Identifier, Type, Expression),
    Assignment(Identifier, Expression),
    IfStatement(Expression, Vec<Statement>, Option<ElseClause>),
    While(Expression, Vec<Statement>),
    Return(Expression),
}

#[derive(Debug, PartialEq)]
pub enum Operator {
    Times,
    Div,
    Plus,
    Minus,
    Not,
    Equal,
    NotEqual,
    And,
    Or,
    Lesser,
    LT,
    Greater,
    GT,
}

impl TryFrom<&Token> for Operator {
    type Error = TreeBuilderError;

    fn try_from(token: &Token) -> Result<Self, Self::Error> {
        let op = match (token.tag.as_str(), token.value.as_str()) {
            ("COMPARISON_OP", "==") => Operator::Equal,
            ("COMPARISON_OP", "!=") => Operator::NotEqual,
            ("COMPARISON_OP", "<") => Operator::Lesser,
            ("COMPARISON_OP", ">") => Operator::Greater,
            ("COMPARISON_OP", "<=") => Operator::LT,
            ("COMPARISON_OP", ">=") => Operator::GT,
            ("TIMES_DIV", "*") => Operator::Times,
            ("TIMES_DIV", "/") => Operator::Div,
            ("PLUS", "+") => Operator::Plus,
            ("MINUS", "-") => Operator::Minus,
            ("AND", "&") => Operator::And,
            ("OR", "|") => Operator::Or,
            ("NEG", "!") => Operator::Not,
            _ => {
                return Err(TreeBuilderError::ShiftError(format!(
                    "While Shifting operator found token: {:?}",
                    token
                )));
            }
        };
        Ok(op)
    }
}

type BExpr = Box<Expression>;

#[derive(Debug, PartialEq)]
pub enum Expression {
    FunCall(Identifier, Vec<Expression>),
    Ident(Identifier),
    Binary(Operator, BExpr, BExpr),
    Unary(Operator, BExpr),
    Lit(Literal),
}

impl Expression {
    fn boxed(self) -> BExpr {
        Box::new(self)
    }
}

#[derive(Debug, PartialEq)]
pub enum Type {
    Int,
    Float,
    Bool,
    Void,
}

impl FromStr for Type {
    type Err = TreeBuilderError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let t = match s {
            "int" => Type::Int,
            "float" => Type::Float,
            "bool" => Type::Bool,
            "void" => Type::Void,
            _ => {
                return Err(TreeBuilderError::ShiftError(format!(
                    "While shifting type found: {:?}",
                    s
                )));
            }
        };
        Ok(t)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier(String);

impl From<&str> for Identifier {
    fn from(ident: &str) -> Self {
        Identifier(ident.to_string())
    }
}

impl FromStr for Identifier {
    type Err = TreeBuilderError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Identifier(s.to_string()))
    }
}

#[derive(Debug, PartialEq)]
pub enum AST {
    Program(Vec<Item>),
    Item(Item),
    Block(Vec<Statement>),
    Identifier(Identifier),
    Statement(Statement),
    Type(Type),
    Expression(Expression),
    Operator(Operator),
    Params(Vec<Param>),
    Arguments(Vec<Expression>),
    Else(ElseClause),
}

impl TreeBuilder for ASTBuilder {
    type Tree = AST;
    fn shift<'a, 'b>(&'a mut self, token: &'b crate::lexer::Token) -> Result<(), TreeBuilderError> {
        let node = match token.tag.as_str() {
            "IDENTIFIER" => Some(token.value.parse().map(AST::Identifier)?),
            "INTEGER_LITERAL" | "FLOAT_LITERAL" | "BOOLEAN_LITERAL" => {
                Some(token.try_into().map(Expression::Lit).map(AST::Expression)?)
            }
            "COMPARISON_OP" | "PLUS" | "MINUS" | "TIMES_DIV" | "NEG" | "AND" | "OR" => {
                Some(token.try_into().map(AST::Operator)?)
            }
            "TYPE" => Some(token.value.parse().map(AST::Type)?),
            "LET" | "LEFT_PAREN" | "RIGHT_PAREN" | "ARROW" | "LEFT_BRACE" | "RIGHT_BRACE"
            | "COLON" | "COMMA" | "SEMI_COLON" | "EQUAL" | "FN" | "IF" | "ELSE" | "WHILE"
            | "RETURN" => None,
            _ => {
                // unimplemented!("Non terminal: {:?}", token)
                return Err(TreeBuilderError::ShiftError(format!(
                    "Unhandled case: {:?}",
                    token
                )));
            }
        };

        if let Some(node) = node {
            self.stack.push(node);
        }

        Ok(())
    }

    fn reduce<'a, 'b>(&'a mut self, production: &'b Production) -> Result<(), TreeBuilderError> {
        let prod = production
            .left
            .unwrap_non_terminal()
            .expect("Left side of production should be non-terminal.");

        match prod {
            // LetDeclaration -> let identifier colon type equal Expression
            "Parameter" => {
                let type_node = self.stack.pop().unwrap();
                let ident_node = self.stack.pop().unwrap();
                match (ident_node, type_node) {
                    (AST::Identifier(ident), AST::Type(typ)) => {
                        let node = AST::Params(vec![Param { ident, typ }]);
                        self.stack.push(node);
                    }
                    _ => unreachable!(),
                }
            }
            "Parameters" => {
                let params = self.stack.pop().unwrap();
                let param = self.stack.pop();
                match (param, params) {
                    (Some(AST::Params(mut p)), AST::Params(mut ps)) => {
                        ps.append(&mut p);
                        let node = AST::Params(ps);
                        self.stack.push(node);
                    }
                    (Some(n), AST::Params(ps)) => {
                        self.stack.push(n);
                        self.stack.push(AST::Params(ps));
                    }
                    o => unreachable!("Found {o:?}"),
                }
            }
            "Arguments" => {
                let arguments = self.stack.pop().unwrap();
                let arg = self.stack.pop();
                match (arg, arguments) {
                    (Some(AST::Expression(e)), AST::Arguments(mut ps)) => {
                        ps.push(e);
                        let node = AST::Arguments(ps);
                        self.stack.push(node);
                    }
                    (Some(n), AST::Expression(e)) => {
                        self.stack.push(n);
                        self.stack.push(AST::Arguments(vec![e]));
                    }
                    o => unreachable!("Found while reducing Arguments {o:?}"),
                }
            }
            "FunctionCall" => {
                if production.right.len() == 4 {
                    let args = self.stack.pop().unwrap();
                    let ident_node = self.stack.pop().unwrap();
                    match (ident_node, args) {
                        (AST::Identifier(ident), AST::Arguments(mut args)) => {
                            args.reverse();
                            let node = AST::Expression(Expression::FunCall(ident, args));
                            self.stack.push(node);
                        }
                        _ => unreachable!(),
                    }
                } else {
                    match self.stack.pop() {
                        Some(AST::Identifier(ident)) => {
                            let node = AST::Expression(Expression::FunCall(ident, vec![]));
                            self.stack.push(node);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            "Literal" | "Expression" | "Statement" => {
                // This reduce instruccions should only "bubble-up" the already constructed
                // ASTs, but it could be a good idea to implement some checks.
                // TODO: add checks
            }
            "Primary" => {
                if let Some(AST::Identifier(_)) = self.stack.last() {
                    if let Some(AST::Identifier(i)) = self.stack.pop() {
                        self.stack.push(AST::Expression(Expression::Ident(i)));
                    }
                }
            }

            "Unary" => {
                if production.right.len() == 2 {
                    match self.get2() {
                        Some((AST::Operator(o), AST::Expression(e))) => {
                            self.stack
                                .push(AST::Expression(Expression::Unary(o, Box::new(e))));
                        }
                        _ => todo!(),
                    }
                }
            }
            "Factor" | "Term" | "Comparison" | "Equality" | "AndExpression" | "OrExpression" => {
                if production.right.len() == 3 {
                    let stack_top = self.get3();
                    match stack_top {
                        Some((AST::Expression(left), AST::Operator(o), AST::Expression(right))) => {
                            self.stack.push(AST::Expression(Expression::Binary(
                                o,
                                left.boxed(),
                                right.boxed(),
                            )));
                        }
                        _ => todo!(),
                    }
                }
            }
            "Item" => match self.stack.pop() {
                Some(AST::Statement(s)) => {
                    self.stack.push(AST::Item(Item::Statement(s)));
                }
                Some(AST::Item(i)) => {
                    self.stack.push(AST::Item(i));
                }
                Some(other) => unreachable!("Processing item got {:?}", other),
                None => unreachable!("Processing item, empty stack"),
            },
            "LetDeclaration" => {
                let exp_node = self.stack.pop().unwrap();
                let type_node = self.stack.pop().unwrap();
                let ident_node = self.stack.pop().unwrap();
                match (ident_node, type_node, exp_node) {
                    (AST::Identifier(ident), AST::Type(typ), AST::Expression(expr)) => {
                        let node = AST::Statement(Statement::Declaration(ident, typ, expr));
                        self.stack.push(node);
                    }
                    _ => {
                        unreachable!("Unhandled reduce while reducing 'LetDeclaration'");
                    }
                }
            }
            "ReturnStatement" => {
                if let Some(AST::Expression(e)) = self.stack.pop() {
                    self.stack.push(AST::Statement(Statement::Return(e)));
                } else {
                    unreachable!("Unhandled reduce while reducing 'Return'")
                }
            }
            "Assignment" => {
                let exp_node = self.stack.pop().unwrap();
                let ident_node = self.stack.pop().unwrap();
                match (ident_node, exp_node) {
                    (AST::Identifier(ident), AST::Expression(expr)) => {
                        let node = AST::Statement(Statement::Assignment(ident, expr));
                        self.stack.push(node);
                    }
                    _ => unreachable!(),
                }
            }
            "WhileLoop" => match self.stack.pop() {
                Some(AST::Block(s)) => {
                    if let Some(AST::Expression(e)) = self.stack.pop() {
                        self.stack.push(AST::Statement(Statement::While(e, s)));
                    }
                }
                _ => unreachable!(),
            },
            "ElseClause" => match self.stack.pop() {
                Some(AST::Block(s)) => {
                    self.stack.push(AST::Else(ElseClause { block: s }));
                }
                _ => unreachable!(),
            },
            "IfStatement" => match self.stack.pop() {
                Some(AST::Else(ec)) => {
                    if let Some(AST::Block(if_block)) = self.stack.pop() {
                        if let Some(AST::Expression(e)) = self.stack.pop() {
                            self.stack.push(AST::Statement(Statement::IfStatement(
                                e,
                                if_block,
                                Some(ec),
                            )));
                        }
                    }
                }
                Some(AST::Block(s)) => {
                    if let Some(AST::Expression(e)) = self.stack.pop() {
                        self.stack
                            .push(AST::Statement(Statement::IfStatement(e, s, None)));
                    }
                }
                _ => unreachable!(),
            },
            // Program -> Item Program | Item
            "Program" => {
                let item_or_prog = self.stack.pop().unwrap();
                match item_or_prog {
                    AST::Item(item) => {
                        let node = AST::Program(vec![item]);
                        self.stack.push(node);
                    }
                    AST::Program(mut program) => {
                        if let AST::Item(item) = self.stack.pop().unwrap() {
                            program.push(item);
                            let node = AST::Program(program);
                            self.stack.push(node);
                        }
                    }
                    _ => unreachable!(),
                }
            }
            "Statements" => {
                let item_or_prog = self.stack.pop().unwrap();
                match item_or_prog {
                    AST::Statement(s) => {
                        let node = AST::Block(vec![s]);
                        self.stack.push(node);
                    }
                    AST::Block(mut statements) => {
                        if let AST::Statement(s) = self.stack.pop().unwrap() {
                            statements.push(s);
                            let node = AST::Block(statements);
                            self.stack.push(node);
                        }
                    }
                    o => unreachable!("Found {o:?} {:?}", self.stack),
                }
            }
            "Block" => {
                if let Some(AST::Block(mut statements)) = self.stack.pop() {
                    statements.reverse();
                    self.stack.push(AST::Block(statements));
                }
            }

            "FunctionDefinition" => {
                let (args_or_ident, return_type, block) = self.get3().unwrap();

                match (args_or_ident, return_type, block) {
                    (AST::Identifier(i), AST::Type(ret), AST::Block(s)) => {
                        self.stack.push(AST::Item(Item::FunDef(FunctionDefinition {
                            ident: i,
                            return_type: ret,
                            arguments: Vec::new(),
                            body: s,
                        })));
                    }
                    (AST::Params(mut args), AST::Type(ret), AST::Block(s)) => {
                        if let Some(AST::Identifier(i)) = self.stack.pop() {
                            args.reverse();
                            self.stack.push(AST::Item(Item::FunDef(FunctionDefinition {
                                ident: i,
                                return_type: ret,
                                arguments: args,
                                body: s,
                            })));
                        }
                    }
                    _ => unreachable!(""),
                }
            }
            other => unreachable!("Trying to reduce with {}.", other),
        }
        Ok(())
    }

    fn to_tree(mut self) -> AST {
        match self.stack.pop() {
            Some(AST::Program(mut items)) => {
                items.reverse();
                AST::Program(items)
            }
            Some(_) => panic!("The top of the stack is not a program!"),
            None => panic!("Empty stack!"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::{
        ast::{AST, ASTBuilder, Expression, Identifier, Item, Literal, Operator, Statement, Type},
        parser::Parser,
    };
    use Expression::*;
    use Operator::*;

    #[test]
    fn parsing_ast_single_statement() {
        let program = "let x: int = 3;";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        let ast = parser.parse(program);

        assert!(ast.is_ok());

        assert_eq!(
            ast.unwrap(),
            AST::Program(vec![Item::Statement(Statement::Declaration(
                Identifier("x".to_string()),
                Type::Int,
                Expression::Lit(Literal::Int(3))
            ))])
        );
    }

    #[test]
    fn parsing_ast_two_statements() {
        let program = "let x: int = 3; let y: bool = true;";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        assert_eq!(
            parser.parse(program),
            Ok(AST::Program(vec![
                Item::Statement(Statement::Declaration(
                    "x".into(),
                    Type::Int,
                    Lit(Literal::Int(3))
                )),
                Item::Statement(Statement::Declaration(
                    "y".into(),
                    Type::Bool,
                    Lit(Literal::Bool(true))
                )),
            ]))
        );
    }

    #[test]
    fn parsing_ast_negative_int_literal() {
        let program = "let x: int = -4;";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        assert_eq!(
            parser.parse(program),
            Ok(AST::Program(vec![Item::Statement(Statement::Declaration(
                "x".into(),
                Type::Int,
                Lit(Literal::Int(-4))
            ))]))
        );
    }

    #[test]
    fn parsing_ast_unary() {
        let program = "let x: int = -(4);";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        assert_eq!(
            parser.parse(program),
            Ok(AST::Program(vec![Item::Statement(Statement::Declaration(
                "x".into(),
                Type::Int,
                Unary(Operator::Minus, Lit(Literal::Int(4)).boxed())
            ))]))
        );
    }

    #[test]
    fn parsing_ast_factor() {
        let program = "let x: int = 3 * 4;";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        assert_eq!(
            parser.parse(program),
            Ok(AST::Program(vec![Item::Statement(Statement::Declaration(
                "x".into(),
                Type::Int,
                Binary(
                    Operator::Times,
                    Lit(Literal::Int(3)).boxed(),
                    Lit(Literal::Int(4)).boxed()
                )
            ))]))
        );
    }

    #[test]
    fn parsing_ast_term() {
        let program = "let x: int = 3 + 4;";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        assert_eq!(
            parser.parse(program),
            Ok(AST::Program(vec![Item::Statement(Statement::Declaration(
                Identifier("x".to_string()),
                Type::Int,
                Binary(
                    Operator::Plus,
                    Lit(Literal::Int(3)).boxed(),
                    Lit(Literal::Int(4)).boxed()
                )
            ))]))
        );
    }

    #[test]
    fn parsing_ast_exhaustive_expression() {
        let program = "let x: int = 3 + -(4) == 0.3 < 5 & true | !false;";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        assert_eq!(
            parser.parse(program),
            Ok(AST::Program(vec![Item::Statement(Statement::Declaration(
                Identifier("x".to_string()),
                Type::Int,
                Binary(
                    Or,
                    Binary(
                        And,
                        Binary(
                            Equal,
                            Binary(
                                Plus,
                                Lit(Literal::Int(3)).boxed(),
                                Unary(Minus, Lit(Literal::Int(4)).boxed()).boxed(),
                            )
                            .boxed(),
                            Binary(
                                Lesser,
                                Lit(Literal::Float(0.3)).boxed(),
                                Lit(Literal::Int(5)).boxed(),
                            )
                            .boxed()
                        )
                        .boxed(),
                        Lit(Literal::Bool(true)).boxed()
                    )
                    .boxed(),
                    Unary(Not, Lit(Literal::Bool(false)).boxed()).boxed()
                )
            ))]))
        );
    }

    #[test]
    fn parsing_ast_function_dec_control_flow() {
        let program = "fn main(x: int) -> void {
        let x: float = -3.0;
        let y: int = 1;
        let z: int = y - 3;
        if (z == y) {
            x = x - 1;
        } else {
            while (true) {
                return false;
            };
        };
    }";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        let ast = parser.parse(program);

        dbg!(&ast);
        assert!(ast.is_ok());
    }

    #[test]
    fn parsing_ast_builder_exhaustive_check() {
        let program = "fn main(x: int, y: bool) -> void {
        let x: float = -3.0;
        let y: int = 1;
        let z: int = y - 3;
        if (z == y) {
            x = x - 1;
        } else {
            while (true) {
                return false;
            };
        };
    let x: bool = g();
    let a: int = f(x);

    let y: bool = true & false | (true & false);

    while true {
        x = f(x,y,z);
    };

    if true {
        x = y;
        x = f(x,y,g(x), x + y);
    };

    if (!true) {
        x = y;
    };

    if true {
        x = y;
    } else {
        x = y;
    };

    let y: bool = !(x == y) & false | (true & false);

    }";
        let parser: Parser<ASTBuilder, AST> = Parser::new();

        let ast = parser.parse(program);

        assert!(ast.is_ok());
        dbg!(ast.unwrap());
    }
}
