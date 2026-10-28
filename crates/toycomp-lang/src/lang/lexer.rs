use toycomp_syntax::Lexer;

/// The lexer specification of the toy language.
///
/// `build.rs` turns this into a static DFA in `$OUT_DIR/lexer_table.rs`.
pub const LEXER_STRING: &str = include_str!("../../spec/toy.lang.lex");

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
    fn non_ascii_is_reported_not_panicked() {
        let lexer: Lexer = LEXER_STRING.parse().unwrap();

        assert!(lexer.consume("let x: int = 1; é").is_err());
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
        assert!(tokens.is_ok());
    }
}
