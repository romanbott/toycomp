use crate::Lexer;
use std::sync::LazyLock;
const LEXER_STRING: &'static str = "ARROW->(->)
BOOLEAN_LITERAL->true|false
COMPARISON_OP->==|<=|>=|!=|<|>
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

pub static LEXER: LazyLock<Lexer> = LazyLock::new(|| LEXER_STRING.parse().unwrap());

#[cfg(test)]
mod tests {
    use super::*;

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
}
