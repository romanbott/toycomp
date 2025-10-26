use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::static_analyzer::grammar::{Production, Symbol};

#[derive(PartialEq, Eq, Hash, Ord, PartialOrd, Clone)]
pub struct LR1Item<'a> {
    prod: Production<'a>,
    dot: usize,
    look_ahead: Symbol<'a>,
}

impl<'a> Debug for LR1Item<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Start of the print: "LR1Item: "
        write!(f, "LR1Item: ")?;

        // Print the left-hand side of the production (X)
        write!(f, "{:?} -> ", self.prod.left)?;

        // --- Print the right-hand side, inserting the dot ---

        // 1. Print symbols BEFORE the dot (ABC)
        // The slice is from index 0 up to (but not including) self.dot
        for symbol in &self.prod.right[..self.dot] {
            write!(f, "{:?}", symbol)?;
        }

        // 2. Insert the dot (.)
        write!(f, "⬤")?;

        // 3. Print symbols AFTER the dot (DEF)
        // The slice is from self.dot to the end
        for symbol in &self.prod.right[self.dot..] {
            write!(f, "{:?}", symbol)?;
        }

        // --- Print the look-ahead ---
        write!(f, ", {:?}", self.look_ahead)
    }
}

impl<'a> LR1Item<'a> {
    pub fn shift<'b>(&self, symbol: &'b Symbol<'a>) -> Option<LR1Item<'a>> {
        if let Some(pointed) = self.get_pointed()
            && pointed == symbol
        {
            return Some(LR1Item {
                prod: self.prod.clone(),
                dot: self.dot + 1,
                look_ahead: self.look_ahead,
            });
        }
        None
    }

    pub fn get_remaining(&self) -> Vec<Symbol> {
        let mut remaining: Vec<_> = self
            .prod
            .right
            .get(self.dot+1..)
            .unwrap_or(&[])
            .iter()
            .map(Symbol::clone)
            .collect();

        remaining.push(self.look_ahead);

        remaining
    }

    pub fn get_pointed(&self) -> Option<&Symbol> {
        self.prod.right.get(self.dot)
    }

    pub fn from_prod_and_la(production: &'a Production, look_ahead: Symbol<'a>) -> Self {
        LR1Item {
            prod: production.clone(),
            dot: 0,
            look_ahead,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct LR1AutomatonState<'a>(pub BTreeSet<LR1Item<'a>>);

#[derive(Debug)]
pub struct LR1Automaton<'a>(pub BTreeSet<LR1AutomatonState<'a>>);

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet};

    use crate::static_analyzer::{
        grammar::{Grammar, Symbol},
        lr_parser::{LR1AutomatonState, LR1Item},
    };

    #[test]
    fn remaining() {
        let grammar = "S -> B B\nB -> b B|d";
        let parsed_grammar = Grammar::from_str(grammar).unwrap();

        let productions = &parsed_grammar.productions;

        let prod = &productions[0];

        let item = LR1Item::from_prod_and_la(prod, Symbol::End);
        let shifted = item.shift(&Symbol::NonTerminal("B")).unwrap();

        let expected_item = LR1Item {
            prod: prod.clone(),
            dot: 0,
            look_ahead: Symbol::End,
        };
        assert_eq!(expected_item, item);

        let expected_shifted = LR1Item {
            prod: prod.clone(),
            dot: 1,
            look_ahead: Symbol::End,
        };

        assert_eq!(expected_shifted, shifted);

        let expected_remaining = vec![Symbol::End];
        assert_eq!(expected_remaining, shifted.get_remaining());
    }

    #[test]
    fn lr1_closure() {
        let grammar = "S -> B B\nB -> b B|d";
        let parsed_grammar = Grammar::from_str(grammar).unwrap();

        let productions = &parsed_grammar.productions;

        let prod = &productions[0];

        let item = LR1Item::from_prod_and_la(prod, Symbol::End);
        let closure = parsed_grammar.lr1_closure(&item);

        let expected_state = LR1AutomatonState(BTreeSet::from([
            LR1Item {
                prod: prod.clone(),
                dot: 0,
                look_ahead: Symbol::End,
            },
            LR1Item {
                prod: productions[1].clone(),
                dot: 0,
                look_ahead: Symbol::Terminal("b"),
            },
            LR1Item {
                prod: productions[1].clone(),
                dot: 0,
                look_ahead: Symbol::Terminal("d"),
            },
            LR1Item {
                prod: productions[2].clone(),
                dot: 0,
                look_ahead: Symbol::Terminal("b"),
            },
            LR1Item {
                prod: productions[2].clone(),
                dot: 0,
                look_ahead: Symbol::Terminal("d"),
            },
        ]));

        assert_eq!(expected_state, closure);

        let item = LR1Item::from_prod_and_la(prod, Symbol::End);

        let shifted = item.shift(&&Symbol::NonTerminal("B"));
        let shifted = shifted.unwrap();

        let closure = parsed_grammar.lr1_closure(&shifted);

        let expected_state = LR1AutomatonState(BTreeSet::from([
            LR1Item {
                prod: productions[0].clone(),
                dot: 1,
                look_ahead: Symbol::End,
            },
            LR1Item {
                prod: productions[1].clone(),
                dot: 0,
                look_ahead: Symbol::End,
            },
            LR1Item {
                prod: productions[2].clone(),
                dot: 0,
                look_ahead: Symbol::End,
            },
        ]));

        assert_eq!(expected_state, closure);
    }

    #[test]
    fn lr1_closure_augmented() {
        let grammar = "S -> B B\nB -> b B|d";
        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let augmented = parsed_grammar.augment();

        let productions = &augmented.productions;

        let prod = &productions[0];

        let item = LR1Item::from_prod_and_la(prod, Symbol::End);
        let closure = parsed_grammar.lr1_closure(&item);

        let expected_state = LR1AutomatonState(BTreeSet::from([
            LR1Item {
                prod: prod.clone(),
                dot: 0,
                look_ahead: Symbol::End,
            },
            LR1Item {
                prod: productions[1].clone(),
                dot: 0,
                look_ahead: Symbol::End,
            },
            LR1Item {
                prod: productions[3].clone(),
                dot: 0,
                look_ahead: Symbol::Terminal("b"),
            },
            LR1Item {
                prod: productions[3].clone(),
                dot: 0,
                look_ahead: Symbol::Terminal("d"),
            },
            LR1Item {
                prod: productions[2].clone(),
                dot: 0,
                look_ahead: Symbol::Terminal("b"),
            },
            LR1Item {
                prod: productions[2].clone(),
                dot: 0,
                look_ahead: Symbol::Terminal("d"),
            },
        ]));

        assert_eq!(expected_state, closure);

    }



    #[test]
    fn goto() {
        let grammar = "S -> B B\nB -> b B|d";
        let parsed_grammar = Grammar::from_str(grammar).unwrap();

        let productions = &parsed_grammar.productions;

        let prod = &productions[0];

        let item = LR1Item::from_prod_and_la(prod, Symbol::End);
        let closure = parsed_grammar.lr1_closure(&item);

        let goto = parsed_grammar.goto(&closure, &Symbol::NonTerminal("B"));

        let expected_state = LR1AutomatonState(BTreeSet::from([
            LR1Item {
                prod: productions[0].clone(),
                dot: 1,
                look_ahead: Symbol::End,
            },
            LR1Item {
                prod: productions[1].clone(),
                dot: 0,
                look_ahead: Symbol::End,
            },
            LR1Item {
                prod: productions[2].clone(),
                dot: 0,
                look_ahead: Symbol::End,
            },
        ]));

        assert_eq!(expected_state, goto);
    }

    #[test]
    fn automaton() {
        let grammar = "S -> B B\nB -> b B|d";
        let parsed_grammar = Grammar::from_str(grammar).unwrap();

        let augmented = parsed_grammar.augment();

        let automaton = augmented.get_lr1_automaton();

        assert_eq!(10, automaton.0.len())
    }
}
