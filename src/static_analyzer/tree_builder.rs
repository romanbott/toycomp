use crate::{lexer::Token, static_analyzer::grammar::Production};

#[derive(Debug)]
pub enum TreeBuilderError {
    ShiftError,
    ReduceError,
}

pub trait TreeBuilder {
    type Tree;
    fn shift<'a, 'b>(&'a mut self, token: &'b Token) -> Result<(), TreeBuilderError>;
    fn reduce<'a, 'b>(&'a mut self, production: &'b Production) -> Result<(), TreeBuilderError>;
    fn to_tree(self) -> Self::Tree;
}

#[derive(Debug)]
pub struct Node {
    value: String,
    children: Vec<Node>,
}

impl Node {
    fn leaf(value: String) -> Self {
        Node {
            value,
            children: Vec::new(),
        }
    }
}

pub struct BasicTreeBuilder {
    stack: Vec<Node>,
}

impl BasicTreeBuilder {
    pub fn new() -> Self {
        BasicTreeBuilder { stack: Vec::new() }
    }
}

impl TreeBuilder for BasicTreeBuilder {
    type Tree = Node;
    fn shift<'a, 'b>(&'a mut self, token: &'b Token) -> Result<(), TreeBuilderError> {
        self.stack.push(Node::leaf(token.tag.clone()));
        return Ok(());
    }

    fn reduce<'a, 'b>(&'a mut self, production: &'b Production) -> Result<(), TreeBuilderError> {
        let to_match = production.right.len();

        let children = self.stack.split_off(self.stack.len() - to_match);

        self.stack.push(Node {
            value: production.left.to_string(),
            children,
        });
        return Ok(());
    }

    fn to_tree(mut self) -> Node {
        self.stack.pop().unwrap()
    }
}
