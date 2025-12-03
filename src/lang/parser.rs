use crate::{
    Lexer, OLALRAutomaton,
    lang::{grammar::LALR, lexer::LEXER},
    static_analyzer::{LALRAutomaton, TreeBuilder},
};

pub struct Parser<T, A>
where
    T: TreeBuilder<Tree = A>,
{
    lexer: Lexer,
    ast_builder: T,
    lalr_automaton: OLALRAutomaton,
}

#[derive(Debug, PartialEq)]
pub struct ParsingError(String);

const EMBEDDED_DATA: &[u8] = include_bytes!("./../../toycomp_lalr_automaton.bin");

impl<T, A> Parser<T, A>
where
    T: TreeBuilder<Tree = A> + Default,
    A: std::fmt::Debug,
{
    pub fn parse(mut self, program: &str) -> Result<A, ParsingError> {
        let tokens = self.lexer.consume(program);
        let mut non_white_space: Vec<_> = tokens
            .unwrap()
            .into_iter()
            .filter(|tok| tok.tag != "WHITE_SPACE")
            .collect();

        let res = self
            .lalr_automaton
            .parse(&mut non_white_space, self.ast_builder);

        res.map_err(|e| ParsingError(e.to_string()))
    }

    pub fn new() -> Self {
        let config = bincode::config::standard();

        let (decoded_automaton, _bytes_consumed) =
            bincode::decode_from_slice::<OLALRAutomaton, _>(EMBEDDED_DATA, config).unwrap();

        // let lalr = &LALR.clone();
        // let automaton: OLALRAutomaton = lalr.into();
        // assert_ne!(decoded_asset, automaton);

        Parser {
            lalr_automaton: decoded_automaton,
            lexer: LEXER.clone(),
            ast_builder: T::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        lang::parser::Parser,
        static_analyzer::{BasicTreeBuilder, Node},
    };

    #[test]
    fn parsing_basic_tree_builder_unary() {
        let program = "let x: int = -(3);";
        let parser: Parser<BasicTreeBuilder, Node> = Parser::new();

        let ast = parser.parse(program);

        dbg!(&ast);
        assert!(ast.is_ok());
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
