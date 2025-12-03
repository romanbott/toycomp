use crate::static_analyzer::{Grammar, LALRAutomaton};
use std::sync::LazyLock;

const GRAMMAR_STRING: &'static str = r#"
Program -> Item Program | Item

Item -> FunctionDefinition | Statement SEMI_COLON

Block -> LEFT_BRACE Statements RIGHT_BRACE

Literal -> INTEGER_LITERAL | BOOLEAN_LITERAL | FLOAT_LITERAL

FunctionDefinition -> FN IDENTIFIER LEFT_PAREN Parameters RIGHT_PAREN ARROW TYPE Block
FunctionDefinition -> FN IDENTIFIER LEFT_PAREN RIGHT_PAREN ARROW TYPE Block

Parameters -> Parameter COMMA Parameters | Parameter

Parameter -> IDENTIFIER COLON TYPE 

FunctionCall -> IDENTIFIER LEFT_PAREN Arguments RIGHT_PAREN
FunctionCall -> IDENTIFIER LEFT_PAREN RIGHT_PAREN

Arguments -> Expression COMMA Arguments | Expression

Statements -> Statement SEMI_COLON Statements | Statement SEMI_COLON

Statement -> LetDeclaration | Assignment | ReturnStatement | IfStatement | WhileLoop

ReturnStatement -> RETURN Expression

LetDeclaration -> LET IDENTIFIER COLON TYPE EQUAL Expression

Assignment -> IDENTIFIER EQUAL Expression

IfStatement -> IF Expression Block | IF Expression Block ElseClause

ElseClause -> ELSE Block

WhileLoop -> WHILE Expression Block

Expression  -> OrExpression

OrExpression  -> AndExpression | OrExpression OR AndExpression

AndExpression  -> Equality | AndExpression AND Equality

Equality -> Comparison EQ_OP Equality | Comparison

Comparison -> Term COMPARISON_OP Comparison | Term

Term -> Factor PLUS Term | Factor MINUS Term | Factor

Factor -> Unary TIMES_DIV Factor | Unary

Unary -> MINUS Unary | NEG Unary | Primary

Primary -> Literal | IDENTIFIER | FunctionCall | LEFT_PAREN Expression RIGHT_PAREN
"#;

static GRAMMAR: LazyLock<Grammar<'static>> =
    LazyLock::new(|| Grammar::from_str(GRAMMAR_STRING).unwrap().augment());

pub static LALR: LazyLock<LALRAutomaton> = LazyLock::new(|| LALRAutomaton::from_grammar(&GRAMMAR));

#[cfg(test)]
mod tests {
    use crate::{lang::grammar::GRAMMAR_STRING, static_analyzer::Grammar};

    #[test]
    fn grammar_parses() {
        let parsed_grammar = Grammar::from_str(GRAMMAR_STRING);
        assert!(parsed_grammar.is_ok());
    }
}
