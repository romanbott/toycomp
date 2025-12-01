use crate::{
    Lexer,
    static_analyzer::{Grammar, LALRAutomaton, Production, TreeBuilder},
};

const GRAMMAR: &'static str = r#"
Program -> Item Program | Item
Item -> FunctionDefinition | Statement semi_colon
Block -> left_brace Statements right_brace
Literal -> integer_literal | float_literal
FunctionDefinition -> fn identifier left_paren Parameters right_paren arrow type Block
FunctionDefinition -> fn identifier left_paren right_paren arrow type Block
Parameters -> Parameter comma Parameters | Parameter
Parameter -> identifier colon type
FunctionCall -> identifier left_paren Arguments right_paren
Arguments -> Expression comma Arguments | Expression
Statements -> Statement semi_colon Statements| Statement semi_colon
Statement -> LetDeclaration | Assignment | ControlFlow | ReturnStatement | IfStatement | WhileLoop
ReturnStatement -> return Expression
LetDeclaration -> let identifier colon type equal Expression
Assignment -> identifier equal Expression
IfStatement -> if left_paren Expression right_paren Block | if left_paren Expression right_paren Block ElseClause
ElseClause -> else Block
WhileLoop -> while left_paren Expression right_paren Block
Expression -> BooleanExpression | AdditiveExpression
BooleanExpression -> AdditiveExpression comparison_op AdditiveExpression | Clause and BooleanExpression | Clause
Clause -> BTerm or Clause | BTerm
BTerm -> boolean_literal | left_paren BooleanExpression rightParen
AdditiveExpression -> MultiplicativeExpression plus_minus AdditiveExpression  | MultiplicativeExpression
MultiplicativeExpression -> PrimaryExpression time_div MultiplicativeExpression  | PrimaryExpression
PrimaryExpression -> Literal | identifier | FunctionCall | left_paren Expression right_paren
// PrimaryExpression -> Literal | identifier | FunctionCall
"#;

const LEXER: &'static str = "arrow->(->)
boolean_literal->true|false
comparison_op->==|<=|>=|!=
and->&
or->\\|
else->else
return->return
equal->=
fn->fn
if->if
left_brace->{
right_brace->}
left_paren->\\(
right_paren->\\)
let->let
plus_minus->\\+|-
semi_colon->;
colon->:
comma->,
time_div->\\*|/
type->int|float|bool|void
while->while
identifier ->(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|_)(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|0|1|2|3|4|5|6|7|8|9)*
float_literal->-?(0|1|2|3|4|5|6|7|8|9)+.(0|1|2|3|4|5|6|7|8|9)*
integer_literal->-?(1|2|3|4|5|6|7|8|9)(0|1|2|3|4|5|6|7|8|9)*
white_space ->\\t|\\r| |\\n";

use std::sync::LazyLock;

static GRAMMAR_STRUCT: LazyLock<Grammar<'static>> =
    LazyLock::new(|| Grammar::from_str(GRAMMAR).unwrap().augment());

static LALR: LazyLock<LALRAutomaton> =
    LazyLock::new(|| LALRAutomaton::from_grammar(&GRAMMAR_STRUCT));

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
            .filter(|tok| tok.tag != "white_space")
            .collect();

        let res = self
            .lalr_automaton
            .parse(&mut non_white_space, self.ast_builder);

        dbg!(&res);
        res.map_err(|_| ParsingError)
    }

    fn new(lexer_spec: &str, grammar_spec: &'a str) -> Self {
        let parsed_grammar = Grammar::from_str(grammar_spec);
        let augmented = parsed_grammar.unwrap().augment();

        Parser {
            lalr_automaton: LALR.clone(),
            lexer: lexer_spec.parse().unwrap(),
            ast_builder: T::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Lexer,
        lang::{GRAMMAR, LEXER, Parser},
        static_analyzer::{BasicTreeBuilder, Grammar, LALRAutomaton, Node},
    };

    #[test]
    fn grammar_parses() {
        let parsed_grammar = Grammar::from_str(GRAMMAR);
        assert!(parsed_grammar.is_ok());
    }

    #[test]
    fn simple_lexing() {
        let lexer: Lexer = LEXER.parse().unwrap();

        let tokens = lexer.consume("fn main() {let x = -302323;}\n if x == y {let y = 0.1}");
        assert!(tokens.is_ok());
    }

    #[test]
    fn complex_lexing() {
        let lexer: Lexer = LEXER.parse().unwrap();

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
        let parser: Parser<BasicTreeBuilder, Node> = Parser::new(LEXER, GRAMMAR);

        let ast = parser.parse(program);

        assert!(ast.is_ok())
    }
}
