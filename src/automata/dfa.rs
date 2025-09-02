use std::{collections::BTreeSet, ops::Index, usize};

use crate::NDFA;

#[derive(Debug, Clone, PartialEq)]
struct LabeledArrow {
    label: char,
    target: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DFA {
    /// Table of transitions, each row represents a state.
    table: Vec<Vec<LabeledArrow>>,
    starting: usize,
    final_states: BTreeSet<usize>,
}

impl From<NDFA> for DFA {
    fn from(ndfa: NDFA) -> Self {
        let alphabet = ndfa.get_alphabet();
        let mut unchecked: BTreeSet<BTreeSet<usize>> = BTreeSet::new();
        let mut checked: BTreeSet<BTreeSet<usize>> = BTreeSet::new();

        let initial_state = ndfa.epsilon_closure(&BTreeSet::from([ndfa.starting]));

        unchecked.insert(initial_state.clone());

        while !unchecked.is_empty() {
            let state = unchecked.pop_first().unwrap();
            checked.insert(state.clone());

            for c in &alphabet {
                let move_c = ndfa.move_c(&state, *c);

                if !move_c.is_empty() & !checked.contains(&move_c) {
                    unchecked.insert(move_c);
                }
            }
        }

        let checked: Vec<BTreeSet<usize>> = checked.into_iter().collect();

        let table = checked
            .iter()
            .map(|s| {
                alphabet
                    .iter()
                    .filter_map(|c| {
                        let moved = ndfa.move_c(s, *c);
                        if moved.is_empty() {
                            None
                        } else {
                            Some(LabeledArrow {
                                label: *c,
                                target: checked.binary_search(&moved).unwrap(),
                            })
                        }
                    })
                    .collect()
            })
            .collect();

        let final_states = checked
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                if s.contains(&ndfa.final_state) {
                    Some(i)
                } else {
                    None
                }
            })
            .collect();

        DFA {
            table,
            starting: checked.binary_search(&initial_state).unwrap(),
            final_states,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::automata::ndfa::Arrow;

    #[test]
    fn test_epsilon_closure() {
        let arrow = Arrow::Epsilon(1);
        let aut = NDFA {
            table: vec![vec![arrow], vec![]],
            starting: 0,
            final_state: 1,
        };

        let dfa: DFA = aut.into();
        dbg!(&dfa);

        let expected = DFA {
            table: vec![vec![]],
            starting: 0,
            final_states: BTreeSet::from([0]),
        };

        assert_eq!(expected, dfa);
    }
}
