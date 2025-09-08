use std::{
    collections::{BTreeMap, BTreeSet},
    usize,
};

use crate::{
    Lexer,
    automata::{Arrow, NDFA, ndfa::NDFATable},
};

/// Represents a Tagged Non-deterministic Finite Automaton (NFA).
/// The automaton is defined by a table of transitions, the starting state, and the final state.
/// Each of the final states has an asociated tag.
#[derive(Debug, Clone)]
pub struct TaggedNDFA {
    /// Table of transitions, each row represents a state.
    pub table: Vec<Vec<Arrow>>,
    pub initial_state: usize,
    pub final_states: BTreeMap<usize, String>,
}

impl From<Lexer> for TaggedNDFA {
    fn from(lexer: Lexer) -> Self {
        let tagged_ndfas: Vec<(String, NDFA)> = lexer
            .patterns
            .iter()
            .map(|p| (p.tag.clone(), NDFA::from_regex(p.regex.as_str())))
            .collect();

        let mut shifted_tables: Vec<NDFATable> = Vec::new();

        let mut total_shift = 0;

        let mut starting_states: Vec<usize> = Vec::new();
        let mut final_states: BTreeMap<usize, String> = BTreeMap::new();

        for (tag, ndfa) in tagged_ndfas {
            starting_states.push(ndfa.starting + total_shift);

            final_states.insert(ndfa.final_state + total_shift, tag);

            shifted_tables.push(
                ndfa.table
                    .iter()
                    .map(|row| {
                        row.iter()
                            .map(|arrow| arrow.move_target(total_shift))
                            .collect()
                    })
                    .collect(),
            );

            total_shift += ndfa.table.len();
        }

        let mut table = shifted_tables.concat();

        // Adds epsilon transitions from a new initial state to all the initial states of
        // the collected NDFAs
        table.push(starting_states.iter().map(|s| Arrow::Epsilon(*s)).collect());

        let initial_state = table.len() - 1;

        TaggedNDFA {
            table,
            initial_state,
            final_states,
        }
    }
}

impl TaggedNDFA {
    /// Simulates one step of the NFA, moving from the current set of states
    /// based on a single character input. Epsilon transitions are not followed.
    pub fn simulate_non_empty_step(&self, states: &BTreeSet<usize>, char: char) -> BTreeSet<usize> {
        states
            .iter()
            .flat_map(|state| {
                self.table[*state]
                    .iter()
                    .filter_map(|arrow| arrow.accept(&char))
            })
            .collect()
    }

    pub fn move_c(&self, states: &BTreeSet<usize>, char: char) -> BTreeSet<usize> {
        self.epsilon_closure(&self.simulate_non_empty_step(states, char))
    }

    /// Computes the epsilon closure of a set of states.
    ///
    /// This finds all states reachable from the initial set of states by following
    /// only epsilon transitions.
    pub fn epsilon_closure(&self, states: &BTreeSet<usize>) -> BTreeSet<usize> {
        let mut unchecked: BTreeSet<usize> = BTreeSet::from_iter(states.clone());

        let mut checked: BTreeSet<usize> = BTreeSet::new();

        while !unchecked.is_empty() {
            let state = unchecked.pop_first().unwrap();
            checked.insert(state);
            for new_state in self.table[state].iter().filter_map(|arrow| arrow.epsilon()) {
                if !unchecked.contains(&new_state) & !checked.contains(&new_state) {
                    unchecked.insert(new_state);
                }
            }
        }

        checked
    }
    pub fn accept(&self, input: &str) -> Option<String> {
        let mut states = BTreeSet::from([self.initial_state]);

        for char in input.chars() {
            states = self.epsilon_closure(&states);
            states = self.simulate_non_empty_step(&states, char);
        }
        states = self.epsilon_closure(&states);

        //TODO: implement priorities for tags when there are different matched tags

        for state in states {
            if let Some(tag) = self.final_states.get(&state) {
                return Some(tag.to_string());
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use crate::{Lexer, lexer::Pattern};

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

        let tagged_ndfa: TaggedNDFA = lex.into();

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

        let tagged_ndfa: TaggedNDFA = lex.into();

        dbg!(&tagged_ndfa);

        assert_eq!(Some("multi b"), tagged_ndfa.accept("bbbb").as_deref());
        assert_eq!(Some("tag1"), tagged_ndfa.accept("bc").as_deref());
        assert_eq!(None, tagged_ndfa.accept("c").as_deref());
    }
}
