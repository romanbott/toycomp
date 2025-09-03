use std::collections::BTreeSet;

use crate::NDFA;

#[derive(Debug, Clone, PartialEq)]
struct LabeledArrow {
    label: char,
    target: usize,
}

impl LabeledArrow {
    fn to_graphviz(&self, source: &usize) -> String {
        format!("{} -> {} [label={}]", source, self.target, self.label)
    }

    fn move_c(&self, char: char) -> Option<usize> {
        if self.label == char {
            Some(self.target)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct DFA {
    /// Table of transitions, each row represents a state.
    table: Vec<Vec<LabeledArrow>>,
    starting: usize,
    final_states: BTreeSet<usize>,
}

impl DFA {
    pub fn move_c(&self, state: usize, char: char) -> Option<usize> {
        self.table[state].iter().find_map(|a| a.move_c(char))
    }

    pub fn accept(&self, input: &str) -> bool {
        let mut state = self.starting;
        for char in input.chars() {
            if let Some(next) = self.move_c(state, char) {
                state = next;
            } else {
                return false;
            }
        }
        self.final_states.contains(&state)
    }

    pub fn from_regex(regex: &str) -> Self {
        NDFA::from_regex(regex).into()
    }

    pub fn to_graphviz(&self) -> String {
        let preamble = r#"digraph {
rankdir = LR;
ranksep = .75;
    node [shape=circle style=filled]
    start [shape=none, label="start", style=""]
"#;

        let arrows: Vec<String> = self
            .table
            .iter()
            .enumerate()
            .map(|(source, trans)| trans.iter().map(move |a| a.to_graphviz(&source)))
            .flatten()
            .collect();

        let final_states: Vec<String> = self
            .final_states
            .iter()
            .map(|fs| format!("{} [shape=doublecircle]", fs))
            .collect();

        format!(
            "{}\n{}\nstart->{}\n{}\n}}",
            preamble,
            final_states.join("\n"),
            self.starting,
            arrows.join("\n")
        )
    }
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
    fn test_basic_to_dfa() {
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

    #[test]
    fn test_dfa_accepts_same_as_ndfa() {
        let dfa = DFA::from_regex("((a*|b)c)*");

        assert!(dfa.accept(""));
        assert!(dfa.accept("bc"));
        assert!(dfa.accept("aaaac"));
        assert!(dfa.accept("aaaacbc"));
        assert!(!dfa.accept("aa"));
    }
}

#[cfg(test)]
mod tests_adrian {

    use super::*;

    #[test]
    fn test_plus() {
        let aut = DFA::from_regex("a+");

        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
        assert!(aut.accept("aaaa"));
        assert!(!aut.accept(""));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_optional() {
        let aut = DFA::from_regex("a?");

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(!aut.accept("aa"));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_union() {
        let aut = DFA::from_regex("a|b");

        assert!(aut.accept("a"));
        assert!(aut.accept("b"));
        assert!(!aut.accept(""));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ab"));
    }

    #[test]
    fn test_precedence_concat_over_union() {
        let aut = DFA::from_regex("ab|c");

        assert!(aut.accept("ab"));
        assert!(aut.accept("c"));
        assert!(!aut.accept("a"));
        assert!(!aut.accept("b"));
        assert!(!aut.accept("ac"));
    }

    #[test]
    fn test_precedence_kleen_over_concat() {
        let aut = DFA::from_regex("ab*c");

        assert!(aut.accept("ac"));
        assert!(aut.accept("abc"));
        assert!(aut.accept("abbbc"));
        assert!(!aut.accept("a"));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ab"));
        assert!(!aut.accept("bc"));
    }

    #[test]
    fn test_grouping_kleene() {
        let aut = DFA::from_regex("(a|b)*");

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(aut.accept("b"));
        assert!(aut.accept("aa"));
        assert!(aut.accept("bb"));
        assert!(aut.accept("ab"));
        assert!(aut.accept("ba"));
        assert!(aut.accept("bababa"));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ac"));
        assert!(!aut.accept("bc"));
    }

    #[test]
    fn test_concat_with_group_union() {
        let aut = DFA::from_regex("a(b|c)d");

        assert!(aut.accept("abd"));
        assert!(aut.accept("acd"));
        assert!(!aut.accept("ad"));
        assert!(!aut.accept("abcd"));
        assert!(!aut.accept("abd d"));
    }

    #[test]
    fn test_complex_nesting() {
        let aut = DFA::from_regex("a(b*|c+)?d");

        assert!(aut.accept("ad"));
        assert!(aut.accept("abd"));
        assert!(aut.accept("abbbd"));
        assert!(aut.accept("acd"));
        assert!(aut.accept("acccd"));
        assert!(!aut.accept("a c d"));
        assert!(!aut.accept("abcd"));
        assert!(!aut.accept("abbc"));
    }

    #[test]
    fn test_nested_kleene() {
        let aut = DFA::from_regex("(a*)*");

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_optional_inside_concat() {
        let aut = DFA::from_regex("a(b?)c");

        assert!(aut.accept("ac"));
        assert!(aut.accept("abc"));
        assert!(!aut.accept("a"));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ab"));
        assert!(!aut.accept("bc"));
    }

    #[test]
    fn test_contains_at_least_one_a() {
        let aut = DFA::from_regex("(a|b)*a(a|b)*");

        let accepted = ["a", "aa", "ab", "ba", "bab", "bbaabb"];
        let rejected = ["", "b", "bb", "bbbb"];

        for input in accepted {
            assert!(aut.accept(input));
        }
        for input in rejected {
            assert!(!aut.accept(input));
        }
    }
}
