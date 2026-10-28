use std::collections::{BTreeMap, BTreeSet};

use crate::automata::{Arrow, NDFA, NDTable};

/// Represents a Tagged Non-deterministic Finite Automaton (NFA).
/// The automaton is defined by a table of transitions, the starting state, and the final state.
/// Each of the final states has an asociated tag.
#[derive(Debug, Clone)]
pub struct TaggedNDFA {
    /// Table of transitions, each row represents a state.
    pub table: NDTable,
    pub initial_state: usize,
    pub final_states: BTreeMap<usize, String>,
}

impl TaggedNDFA {
    #[allow(dead_code)]
    pub fn accept(&self, input: &str) -> Option<String> {
        let mut states = BTreeSet::from([self.initial_state]);

        for char in input.chars() {
            states = self.table.epsilon_closure(&states);
            states = self.table.simulate_non_empty_step(&states, char);
        }
        states = self.table.epsilon_closure(&states);

        //TODO: implement priorities for tags when there are different matched tags

        for state in states {
            if let Some(tag) = self.final_states.get(&state) {
                return Some(tag.to_string());
            }
        }

        None
    }

    pub fn worklist(&self) -> (Vec<Vec<(char, usize)>>, usize, BTreeMap<usize, String>) {
        let initial_state = self
            .table
            .epsilon_closure(&BTreeSet::from([self.initial_state]));
        let checked: Vec<BTreeSet<usize>> = self
            .table
            .worklist(self.initial_state)
            .into_iter()
            .collect();
        let alphabet = self.table.get_alphabet();

        let table = checked
            .iter()
            .map(|source| {
                alphabet
                    .iter()
                    .filter_map(|c| {
                        checked
                            .binary_search(&self.table.move_c(source, *c))
                            .ok()
                            .map(|target| (*c, target))
                    })
                    .collect()
            })
            .collect();

        let final_states: BTreeMap<usize, String> = checked
            .iter()
            .enumerate()
            .filter_map(|(i, states)| {
                states
                    .iter()
                    .filter_map(|s| self.final_states.get(s).cloned())
                    .next()
                    .map(|l| (i, l))
            })
            .collect();

        (
            table,
            checked.binary_search(&initial_state).unwrap(),
            final_states,
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::{Lexer, Pattern};

    use super::TaggedNDFA;

    #[test]
    fn tagged_from_lexer() {
        let lex = Lexer {
            patterns: vec![
                Pattern {
                    regex: "a".to_string(),
                    tag: "single_a".to_string(),
                },
                Pattern {
                    regex: "b".to_string(),
                    tag: "single_b".to_string(),
                },
            ],
        };

        let tagged_ndfa: TaggedNDFA = (&lex).into();

        dbg!(&tagged_ndfa);

        assert_eq!(Some("single_a"), tagged_ndfa.accept("a").as_deref());
        assert_eq!(Some("single_b"), tagged_ndfa.accept("b").as_deref());
        assert_eq!(None, tagged_ndfa.accept("c").as_deref());
    }

    #[test]
    fn tagged_from_lexer2() {
        let lex = Lexer {
            patterns: vec![
                Pattern {
                    regex: "(a|b)c".to_string(),
                    tag: "tag1".to_string(),
                },
                Pattern {
                    regex: "b*".to_string(),
                    tag: "multi b".to_string(),
                },
            ],
        };

        let tagged_ndfa: TaggedNDFA = (&lex).into();

        dbg!(&tagged_ndfa);

        assert_eq!(Some("multi b"), tagged_ndfa.accept("bbbb").as_deref());
        assert_eq!(Some("tag1"), tagged_ndfa.accept("bc").as_deref());
        assert_eq!(None, tagged_ndfa.accept("c").as_deref());
    }
}
