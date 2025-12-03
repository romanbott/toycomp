use serde::{Deserialize, Serialize};
use std::{collections::HashMap, fmt};

use crate::{
    lexer::Token,
    static_analyzer::{
        LALRAutomaton, Production, TreeBuilder,
        grammar::Symbol,
        lalr::{LALRAction, ParseError},
    },
};

/// Represents a symbol in a formal grammar.
///
/// Symbols can be either a `Terminal`, a `NonTerminal`, or the special `End`
/// symbol which signifies the end of the input stream.
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OSymbol {
    kind: String,
    value: String,
}

impl fmt::Display for OSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{}, '{}'>", self.kind, self.value)
    }
}

impl<'a> From<&Symbol<'a>> for OSymbol {
    fn from(value: &Symbol) -> Self {
        match value {
            Symbol::Terminal(s) => OSymbol {
                kind: "Terminal".to_string(),
                value: s.to_string(),
            },
            Symbol::NonTerminal(s) => OSymbol {
                kind: "NonTerminal".to_string(),
                value: s.to_string(),
            },
            Symbol::Start => OSymbol {
                kind: "Start".to_string(),
                value: "".to_string(),
            },
            Symbol::End => OSymbol {
                kind: "End".to_string(),
                value: "".to_string(),
            },
            Symbol::Epsilon => OSymbol {
                kind: "Epsilon".to_string(),
                value: "".to_string(),
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Ord, PartialOrd, Clone, Serialize, Deserialize)]
pub struct OProduction {
    /// The non-terminal symbol on the left side of the production.
    pub left: OSymbol,
    /// The sequence of symbols on the right side of the production.
    pub right: Vec<OSymbol>,
}

impl<'a> From<&Production<'a>> for OProduction {
    fn from(prod: &Production<'a>) -> Self {
        OProduction {
            left: (&prod.left).into(),
            right: prod.right.iter().map(OSymbol::from).collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
enum OLALRAction {
    Shift(usize),
    Reduce(OProduction),
    Accept,
    Goto(usize),
}

impl OLALRAction {
    pub fn goto(&self) -> Option<usize> {
        match self {
            OLALRAction::Goto(new_state) => Some(*new_state),
            _ => None,
        }
    }
}

impl<'a> From<&LALRAction<'a>> for OLALRAction {
    fn from(action: &LALRAction) -> Self {
        match action {
            LALRAction::Shift(n) => OLALRAction::Shift(*n),
            LALRAction::Reduce(production) => OLALRAction::Reduce(production.into()),
            LALRAction::Accept => OLALRAction::Accept,
            LALRAction::Goto(n) => OLALRAction::Goto(*n),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct Key(usize, String, String);

#[derive(Debug, Eq, PartialEq)]
pub struct KeyRef<'a> {
    pub num: usize,
    pub s1: &'a str,
    pub s2: &'a str,
}

// Implement Hash for the lookup key (KeyRef)
impl std::hash::Hash for KeyRef<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.num.hash(state);
        self.s1.hash(state);
        self.s2.hash(state);
    }
}

use std::borrow::Borrow;

// Implement Borrow for the owned key type
impl<'a> Borrow<KeyRef<'a>> for Key {
    // The borrow method must return `&Q`, where Q is KeyRef<'_>
    fn borrow(&self) -> &KeyRef<'a> {
        // This is a common, though technically unsafe, pattern used in Rust
        // for composite keys to avoid complex lifetimes or allocating.
        // It converts a reference to the owned Key struct into a reference
        // to the borrowed KeyRef struct, aligning the data.
        unsafe { &*(self as *const Key as *const KeyRef<'_>) }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OLALRAutomaton {
    table: HashMap<Key, OLALRAction>,
    initial_state: usize,
    terminals: Vec<OSymbol>,
}

impl<'a> From<&LALRAutomaton<'a>> for OLALRAutomaton {
    fn from(aut: &LALRAutomaton<'a>) -> Self {
        let table: HashMap<_, _> = aut
            .table
            .iter()
            .map(|((n, s), v)| {
                let symbol: (String, String) = s.into();
                (Key(*n, symbol.0, symbol.1), v.into())
            })
            .collect();

        OLALRAutomaton {
            table,
            initial_state: aut.initial_state,
            terminals: aut.terminals.iter().map(OSymbol::from).collect(),
        }
    }
}

impl OLALRAutomaton {
    pub fn parse<'b, T>(
        &self,
        input: &mut Vec<Token>,
        mut symbol_stack: impl TreeBuilder<Tree = T>,
    ) -> Result<T, ParseError> {
        let mut state_stack = vec![self.initial_state];

        input.push(Token {
            tag: "<END>".to_string(),
            value: "".to_string(),
            // TODO: fix this position
            position: (0, 0),
        });

        input.reverse();

        while let Some(token) = input.last() {
            let current_state = state_stack.last().expect("Empty state stack!");

            let key = KeyRef {
                num: *current_state,
                s1: "Terminal",
                s2: &token.tag,
            };
            let action = self.table.get(&key);

            match action {
                Some(OLALRAction::Shift(new_state)) => {
                    symbol_stack.shift(token)?;
                    state_stack.push(*new_state);
                    input.pop();
                }
                Some(OLALRAction::Reduce(production)) => {
                    let to_match = production.right.len();

                    symbol_stack.reduce(&production.left.value, to_match)?;
                    state_stack.truncate(state_stack.len() - to_match);

                    let current_state = state_stack.last().expect("Empty state stack!");

                    let key = KeyRef {
                        num: *current_state,
                        s1: &production.left.kind,
                        s2: &production.left.value,
                    };

                    let action = self.table.get(&key).unwrap();
                    state_stack.push(action.goto().unwrap());
                }
                Some(OLALRAction::Accept) => return Ok(symbol_stack.to_tree()),
                Some(OLALRAction::Goto(new_state)) => {
                    symbol_stack.shift(token)?;
                    state_stack.push(*new_state);
                    input.pop();
                }
                None => {
                    let expected_symbols = self
                        .terminals
                        .iter()
                        .filter(|s| {
                            let key = KeyRef {
                                num: *current_state,
                                s1: &s.kind,
                                s2: &s.value,
                            };

                            self.table.get(&key).is_some()
                        })
                        .map(OSymbol::to_string)
                        .collect();

                    return Err(ParseError::NotExpectedVerbose((
                        token.clone(),
                        expected_symbols,
                    )));
                }
            }
        }
        Err(ParseError::EndWhileParsing)
    }
}
