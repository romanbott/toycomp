//! Compact, statically-generated LALR(1) tables.
//!
//! `TableData` is what `build.rs` (or `parsergen`) computes from a grammar.
//! `Table` is the `&'static` form that gets emitted as a Rust source file and
//! included by the compiler. There is no serialization format involved.

use std::collections::HashMap;
use std::fmt::Write as _;

use crate::{
    grammar::{Grammar, Production, Symbol},
    lalr::{LALRAction, LALRAutomaton, ParseError},
    lexer::Token,
    tree_builder::TreeBuilder,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    Error,
    Shift(u16),
    Reduce(u16),
    Accept,
}

/// A generated parser table. Every slice lives for the whole program.
pub struct Table {
    pub initial_state: u16,
    pub n_terminals: u16,
    pub n_nonterminals: u16,
    /// `n_states * n_terminals` entries, row-major.
    pub action: &'static [Action],
    /// `n_states * n_nonterminals` entries, row-major. `u16::MAX` means none.
    pub goto: &'static [u16],
    pub prod_lhs: &'static [u16],
    pub prod_rhs_len: &'static [u16],
    /// Raw token tags, e.g. `IF`, `IDENTIFIER`, `<END>`.
    pub terminal_tags: &'static [&'static str],
    /// Non-terminal names, indexed by production LHS id.
    pub nonterminal_names: &'static [&'static str],
}

impl Table {
    pub fn parse<A>(
        &self,
        input: &mut Vec<Token>,
        mut tree: impl TreeBuilder<Tree = A>,
    ) -> Result<A, ParseError> {
        let mut state_stack: Vec<u16> = vec![self.initial_state];

        input.push(Token::from(("<END>", "")));
        input.reverse();

        while let Some(token) = input.last() {
            let state = *state_stack.last().expect("Empty state stack!") as usize;
            let term = match self.terminal_index(&token.tag) {
                Some(term) => term,
                None => {
                    return Err(ParseError::NotExpectedVerbose((
                        token.clone(),
                        self.expected(state),
                    )));
                }
            };

            let action = self.action[state * self.n_terminals as usize + term];
            match action {
                Action::Shift(next) => {
                    tree.shift(token)?;
                    state_stack.push(next);
                    input.pop();
                }
                Action::Reduce(prod) => {
                    let lhs = self.prod_lhs[prod as usize];
                    let len = self.prod_rhs_len[prod as usize] as usize;

                    tree.reduce(self.nonterminal_names[lhs as usize], len)?;
                    state_stack.truncate(state_stack.len() - len);

                    let state = *state_stack.last().expect("Empty state stack!") as usize;
                    let next = self.goto[state * self.n_nonterminals as usize + lhs as usize];
                    if next == u16::MAX {
                        return Err(ParseError::CantReduce(format!(
                            "no goto for {} in state {}",
                            self.nonterminal_names[lhs as usize], state
                        )));
                    }
                    state_stack.push(next);
                }
                Action::Accept => return Ok(tree.to_tree()),
                Action::Error => {
                    return Err(ParseError::NotExpectedVerbose((
                        token.clone(),
                        self.expected(state),
                    )));
                }
            }
        }

        Err(ParseError::EndWhileParsing)
    }

    fn terminal_index(&self, tag: &str) -> Option<usize> {
        self.terminal_tags.iter().position(|t| *t == tag)
    }

    fn expected(&self, state: usize) -> Vec<String> {
        (0..self.n_terminals as usize)
            .filter(|&i| self.action[state * self.n_terminals as usize + i] != Action::Error)
            .map(|i| {
                let tag = self.terminal_tags[i];
                if tag == "<END>" {
                    "<EOF>".to_string()
                } else {
                    format!("'{tag}'")
                }
            })
            .collect()
    }
}

/// Owned table data, used by the generators.
pub struct TableData {
    pub initial_state: u16,
    pub n_terminals: u16,
    pub n_nonterminals: u16,
    pub action: Vec<Action>,
    pub goto: Vec<u16>,
    pub prod_lhs: Vec<u16>,
    pub prod_rhs_len: Vec<u16>,
    pub terminal_tags: Vec<String>,
    pub nonterminal_names: Vec<String>,
}

impl TableData {
    pub fn from_lalr(grammar: &Grammar<'_>, lalr: &LALRAutomaton<'_>) -> Self {
        let terminals: Vec<Symbol> = lalr.terminals.clone();
        let nonterminals: Vec<Symbol> = grammar.non_terminals.iter().copied().collect();

        let term_ids: HashMap<Symbol, u16> = terminals
            .iter()
            .enumerate()
            .map(|(i, s)| (*s, i as u16))
            .collect();
        let nt_ids: HashMap<Symbol, u16> = nonterminals
            .iter()
            .enumerate()
            .map(|(i, s)| (*s, i as u16))
            .collect();
        let prod_ids: HashMap<Production, u16> = grammar
            .productions
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, p)| (p, i as u16))
            .collect();

        let n_terminals = terminals.len() as u16;
        let n_nonterminals = nonterminals.len() as u16;
        let n_prods = grammar.productions.len();
        let n_states = lalr
            .table
            .keys()
            .map(|(state, _)| *state)
            .max()
            .unwrap_or(lalr.initial_state)
            + 1;

        let mut action = vec![Action::Error; n_states * n_terminals as usize];
        let mut goto = vec![u16::MAX; n_states * n_nonterminals as usize];

        for ((state, symbol), act) in &lalr.table {
            let state = *state;
            match act {
                LALRAction::Shift(next) => {
                    let term = term_ids[symbol] as usize;
                    action[state * n_terminals as usize + term] = Action::Shift(*next as u16);
                }
                LALRAction::Reduce(prod) => {
                    let term = term_ids[symbol] as usize;
                    let prod = prod_ids[prod];
                    action[state * n_terminals as usize + term] = Action::Reduce(prod);
                }
                LALRAction::Accept => {
                    let term = term_ids[symbol] as usize;
                    action[state * n_terminals as usize + term] = Action::Accept;
                }
                LALRAction::Goto(next) => {
                    let nt = nt_ids[symbol] as usize;
                    goto[state * n_nonterminals as usize + nt] = *next as u16;
                }
            }
        }

        let prod_lhs: Vec<u16> = grammar
            .productions
            .iter()
            .map(|p| nt_ids[&p.left])
            .collect();
        let prod_rhs_len: Vec<u16> = grammar
            .productions
            .iter()
            .map(|p| p.right.len() as u16)
            .collect();

        debug_assert_eq!(prod_lhs.len(), n_prods);
        debug_assert_eq!(prod_rhs_len.len(), n_prods);

        TableData {
            initial_state: lalr.initial_state as u16,
            n_terminals,
            n_nonterminals,
            action,
            goto,
            prod_lhs,
            prod_rhs_len,
            terminal_tags: terminals.iter().map(symbol_name).collect(),
            nonterminal_names: nonterminals.iter().map(symbol_name).collect(),
        }
    }

    pub fn to_rust_source(&self) -> String {
        let mut out = String::new();

        out.push_str("use toycomp_syntax::{Action, Table};\n\n");
        out.push_str("pub static TABLE: Table = Table {\n");
        writeln!(out, "    initial_state: {},", self.initial_state).unwrap();
        writeln!(out, "    n_terminals: {},", self.n_terminals).unwrap();
        writeln!(out, "    n_nonterminals: {},", self.n_nonterminals).unwrap();

        out.push_str("    action: &[\n");
        for (i, action) in self.action.iter().enumerate() {
            if i % 10 == 0 {
                out.push_str("        ");
            }
            out.push_str(&action_source(*action));
            out.push_str(", ");
            if i % 10 == 9 {
                out.push('\n');
            }
        }
        out.push_str("\n    ],\n");

        out.push_str("    goto: &[\n");
        for (i, state) in self.goto.iter().enumerate() {
            if i % 20 == 0 {
                out.push_str("        ");
            }
            write!(out, "{state}, ").unwrap();
            if i % 20 == 19 {
                out.push('\n');
            }
        }
        out.push_str("\n    ],\n");

        writeln!(out, "    prod_lhs: &{:?},", self.prod_lhs).unwrap();
        writeln!(out, "    prod_rhs_len: &{:?},", self.prod_rhs_len).unwrap();

        out.push_str("    terminal_tags: &[");
        for (i, tag) in self.terminal_tags.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            write!(out, "{tag:?}").unwrap();
        }
        out.push_str("],\n");

        out.push_str("    nonterminal_names: &[");
        for (i, name) in self.nonterminal_names.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            write!(out, "{name:?}").unwrap();
        }
        out.push_str("],\n");

        out.push_str("};\n");
        out
    }
}

fn symbol_name(symbol: &Symbol<'_>) -> String {
    match symbol {
        Symbol::Terminal(name) => (*name).to_string(),
        Symbol::NonTerminal(name) => (*name).to_string(),
        Symbol::End => "<END>".to_string(),
        Symbol::Start => "Start".to_string(),
        Symbol::Epsilon => "epsilon".to_string(),
    }
}

fn action_source(action: Action) -> String {
    match action {
        Action::Error => "Action::Error".to_string(),
        Action::Shift(state) => format!("Action::Shift({state})"),
        Action::Reduce(prod) => format!("Action::Reduce({prod})"),
        Action::Accept => "Action::Accept".to_string(),
    }
}
