mod ast;

use crate::{
    Lexer,
    static_analyzer::{Grammar, LALRAutomaton, Production, TreeBuilder},
};

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

Unary -> MINUS Unary | NEG Unary |Primary

Primary -> Literal | IDENTIFIER | FunctionCall | LEFT_PAREN Expression RIGHT_PAREN
"#;

const LEXER_STRING: &'static str = "ARROW->(->)
BOOLEAN_LITERAL->true|false
COMPARISON_OP->==|<=|>=|!=
NEG->!
AND->&
OR->\\|
ELSE->else
RETURN->return
EQUAL->=
FN->fn
IF->if
LEFT_BRACE->{
RIGHT_BRACE->}
LEFT_PAREN->\\(
RIGHT_PAREN->\\)
LET->let
PLUS->\\+
MINUS->-
SEMI_COLON->;
COLON->:
COMMA->,
TIMES_DIV->\\*|/
TYPE->int|float|bool|void
WHILE->while
IDENTIFIER ->(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|_)(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|0|1|2|3|4|5|6|7|8|9)*
FLOAT_LITERAL->-?(0|1|2|3|4|5|6|7|8|9)+.(0|1|2|3|4|5|6|7|8|9)*
INTEGER_LITERAL->-?(1|2|3|4|5|6|7|8|9)(0|1|2|3|4|5|6|7|8|9)*
WHITE_SPACE ->\\t|\\r| |\\n";

use std::sync::LazyLock;

static GRAMMAR: LazyLock<Grammar<'static>> =
    LazyLock::new(|| Grammar::from_str(GRAMMAR_STRING).unwrap().augment());

static LALR: LazyLock<LALRAutomaton> = LazyLock::new(|| LALRAutomaton::from_grammar(&GRAMMAR));

static LEXER: LazyLock<Lexer> = LazyLock::new(|| LEXER_STRING.parse().unwrap());

struct Parser<'a, T, A>
where
    T: TreeBuilder<Tree = A>,
{
    lexer: Lexer,
    ast_builder: T,
    lalr_automaton: LALRAutomaton<'a>,
}

#[derive(Debug)]
struct ParsingError;

impl<'a, T, A> Parser<'a, T, A>
where
    T: TreeBuilder<Tree = A> + Default,
    A: std::fmt::Debug,
{
    fn parse(mut self, program: &str) -> Result<A, ParsingError> {
        let tokens = self.lexer.consume(program);
        let mut non_white_space: Vec<_> = tokens
            .unwrap()
            .into_iter()
            .filter(|tok| tok.tag != "WHITE_SPACE")
            .collect();

        let res = self
            .lalr_automaton
            .parse(&mut non_white_space, self.ast_builder);

        dbg!(&res);
        res.map_err(|_| ParsingError)
    }

    fn new() -> Self {
        Parser {
            lalr_automaton: LALR.clone(),
            lexer: LEXER.clone(),
            ast_builder: T::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Lexer,
        lang::{GRAMMAR_STRING, LEXER_STRING, Parser},
        static_analyzer::{BasicTreeBuilder, Grammar, Node},
    };

    #[test]
    fn grammar_parses() {
        let parsed_grammar = Grammar::from_str(GRAMMAR_STRING);
        assert!(parsed_grammar.is_ok());
    }

    #[test]
    fn simple_lexing() {
        let lexer: Lexer = LEXER_STRING.parse().unwrap();

        let tokens = lexer.consume("fn main() {let x = -302323;}\n if x == y {let y = 0.1}");
        assert!(tokens.is_ok());
    }

    #[test]
    fn complex_lexing() {
        let lexer: Lexer = LEXER_STRING.parse().unwrap();

        let program = "fn main(x: int) -> void {
    let x = -3.0;
    let y = 1;
    let z = y - 3;
    if z == y {
        x = x - 1;
    } else {
        while true {
            return false;
        }
    }
}";

        let tokens = lexer.consume(program);
    }

    #[test]
    fn parsing_basic_tree_builder() {
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
        let parser: Parser<BasicTreeBuilder, Node> = Parser::new();

        let ast = parser.parse(program);

        assert!(ast.is_ok())
    }

    #[test]
    fn parsing_basic_tree_builder_exhaustive_check() {
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
let x: bool = true;
let a: int = -y;

let y: bool = true & false | (true & false);

while true {
    x = y;
};

if true {
    x = y;
};

if (true) {
    x = y;
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
        let parser: Parser<BasicTreeBuilder, Node> = Parser::new();

        let ast = parser.parse(program);

        assert!(ast.is_ok())
    }
}
