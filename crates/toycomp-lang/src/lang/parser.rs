use toycomp_syntax::{Lexer, StaticDFA, Table, TreeBuilder};

mod lalr_table {
    include!(concat!(env!("OUT_DIR"), "/lalr_table.rs"));
}

mod lexer_table {
    include!(concat!(env!("OUT_DIR"), "/lexer_table.rs"));
}

pub struct Parser<T, A>
where
    T: TreeBuilder<Tree = A>,
{
    dfa: &'static StaticDFA,
    table: &'static Table,
    ast_builder: T,
}

#[derive(Debug, PartialEq)]
pub struct ParsingError(String);

impl<T, A> Parser<T, A>
where
    T: TreeBuilder<Tree = A> + Default,
    A: std::fmt::Debug,
{
    pub fn parse(self, program: &str) -> Result<A, ParsingError> {
        let tokens = Lexer::scan(self.dfa, program).map_err(|e| ParsingError(e.to_string()))?;

        let mut non_white_space: Vec<_> = tokens
            .into_iter()
            .filter(|tok| tok.tag != "WHITE_SPACE")
            .collect();

        let res = self.table.parse(&mut non_white_space, self.ast_builder);

        res.map_err(|e| ParsingError(e.to_string()))
    }

    pub fn new() -> Self {
        Parser {
            dfa: &lexer_table::DFA,
            table: &lalr_table::TABLE,
            ast_builder: T::default(),
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
