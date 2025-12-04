use std::{fmt::Display, str::FromStr};

use crate::{lexer::Token, static_analyzer::TreeBuilderError};

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

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier(pub String);

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Int,
    Float,
    Bool,
    Void,
}

impl Type {
    pub fn is_bool(&self) -> bool {
        matches!(self, Type::Bool)
    }
}

#[derive(Debug, PartialEq)]
pub enum Item {
    FunDef(FunctionDefinition),
    Statement(Statement),
}

#[derive(Debug, PartialEq)]
pub struct FunctionDefinition {
    pub ident: Identifier,
    pub return_type: Type,
    pub arguments: Vec<Param>,
    pub body: Vec<Statement>,
}

#[derive(Debug, PartialEq)]
pub struct Param {
    pub ident: Identifier,
    pub typ: Type,
}

#[derive(Debug, PartialEq)]
pub enum Literal {
    Int(i64),
    Bool(bool),
    Float(f64),
}

impl Literal {
    pub fn get_type(&self) -> Type {
        match self {
            Literal::Int(_) => Type::Int,
            Literal::Bool(_) => Type::Bool,
            Literal::Float(_) => Type::Float,
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Int(v) => write!(f, "{v}"),
            Literal::Bool(v) => write!(f, "{v}"),
            Literal::Float(v) => write!(f, "{v}"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct ElseClause(pub Vec<Statement>);

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
    LTE,
    Greater,
    GTE,
    Mod,
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

impl Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operator::Plus => write!(f, "ADD"),
            // MUL
            Operator::Times => write!(f, "MUL"),
            // DIV
            Operator::Div => write!(f, "DIV"),
            // SUB
            Operator::Minus => write!(f, "SUB"),
            // NOT
            Operator::Not => write!(f, "NOT"),
            // EQ
            Operator::Equal => write!(f, "EQ"),
            // NEQ
            Operator::NotEqual => write!(f, "NEQ"),
            // AND
            Operator::And => write!(f, "AND"),
            // OR
            Operator::Or => write!(f, "OR"),
            // LT
            Operator::Lesser => write!(f, "LT"),
            // LTE
            Operator::LTE => write!(f, "LTE"),
            // GT
            Operator::Greater => write!(f, "GT"),
            // GTE
            Operator::GTE => write!(f, "GTE"),
            // MOD
            Operator::Mod => write!(f, "MOD"),
            // MOD
        }
    }
}

impl TryFrom<&Token> for Operator {
    type Error = TreeBuilderError;

    fn try_from(token: &Token) -> Result<Self, Self::Error> {
        let op = match (token.tag.as_str(), token.value.as_str()) {
            ("COMPARISON_OP", "==") => Operator::Equal,
            ("COMPARISON_OP", "!=") => Operator::NotEqual,
            ("COMPARISON_OP", "<") => Operator::Lesser,
            ("COMPARISON_OP", ">") => Operator::Greater,
            ("COMPARISON_OP", "<=") => Operator::LTE,
            ("COMPARISON_OP", ">=") => Operator::GTE,
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
    pub fn boxed(self) -> BExpr {
        Box::new(self)
    }
}

impl From<i64> for BExpr {
    fn from(value: i64) -> Self {
        Expression::Lit(Literal::Int(value)).boxed()
    }
}

impl From<i64> for Expression {
    fn from(value: i64) -> Self {
        Expression::Lit(Literal::Int(value))
    }
}

impl From<f64> for BExpr {
    fn from(value: f64) -> Self {
        Expression::Lit(Literal::Float(value)).boxed()
    }
}

impl From<bool> for BExpr {
    fn from(value: bool) -> Self {
        Expression::Lit(Literal::Bool(value)).boxed()
    }
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
