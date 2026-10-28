use toycomp_syntax::{Lexer, OLALRAutomaton, TaggedDFA, TreeBuilder};

use crate::lang::lexer::LEXER;

pub struct Parser<T, A>
where
    T: TreeBuilder<Tree = A>,
{
    lexer: Lexer,
    dfa: TaggedDFA,
    ast_builder: T,
    lalr_automaton: OLALRAutomaton,
}

#[derive(Debug, PartialEq)]
pub struct ParsingError(String);

const LALR_BYTES: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/lalr.bin"));
const LEXER_BYTES: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/lexer.bin"));

impl<T, A> Parser<T, A>
where
    T: TreeBuilder<Tree = A> + Default,
    A: std::fmt::Debug,
{
    pub fn parse(self, program: &str) -> Result<A, ParsingError> {
        let tokens = self
            .lexer
            .consume_with(&self.dfa, program)
            .map_err(|e| ParsingError(e.to_string()))?;

        let mut non_white_space: Vec<_> = tokens
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

        let (lalr_automaton, _) =
            bincode::decode_from_slice::<OLALRAutomaton, _>(LALR_BYTES, config).unwrap();
        let (dfa, _) = bincode::decode_from_slice::<TaggedDFA, _>(LEXER_BYTES, config).unwrap();

        Parser {
            lexer: LEXER.clone(),
            dfa,
            ast_builder: T::default(),
            lalr_automaton,
        }
    }
}

#[cfg(test)]
mod tests {
    use toycomp_syntax::{BasicTreeBuilder, Node};

    use crate::lang::parser::Parser;

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
