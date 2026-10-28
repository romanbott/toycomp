//! The toy language: grammar, lexer spec, AST, type checker and code generator.

mod lang;
mod semantic_analyzer;

pub use lang::AST;
pub use lang::ASTBuilder;
pub use lang::Codegen;
pub use lang::Expression;
pub use lang::FunctionDefinition;
pub use lang::GRAMMAR;
pub use lang::Item;
pub use lang::Operator;
pub use lang::Parser;
pub use lang::Statement;
pub use lang::Type;
pub use semantic_analyzer::TypeChecker;
pub use semantic_analyzer::TypeChekingError;
