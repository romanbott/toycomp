use crate::{
    Lexer,
    lang::{grammar::LALR, lexer::LEXER},
    static_analyzer::{LALRAutomaton, TreeBuilder},
};

pub struct Parser<'a, T, A>
where
    T: TreeBuilder<Tree = A>,
{
    lexer: Lexer,
    ast_builder: T,
    lalr_automaton: LALRAutomaton<'a>,
}

#[derive(Debug, PartialEq)]
pub struct ParsingError(String);

impl<'a, T, A> Parser<'a, T, A>
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
