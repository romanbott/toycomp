use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::{Lexer, NDFA};

use super::tagged_ndfa::TaggedNDFA;

use itertools::Itertools;

#[derive(Debug, Clone, PartialEq)]
pub struct LabeledArrow {
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

impl From<(char, usize)> for LabeledArrow {
    fn from(value: (char, usize)) -> Self {
        LabeledArrow {
            label: value.0,
            target: value.1,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct DTable(pub Vec<Vec<LabeledArrow>>);

impl DTable {
    pub fn get_alphabet(&self) -> BTreeSet<char> {
        self.0
            .iter()
            .flat_map(|row| row.iter().map(|a| a.label))
            .collect()
    }

    pub fn move_c(&self, state: usize, char: char) -> Option<usize> {
        self.0[state].iter().find_map(|a| a.move_c(char))
    }

    pub fn get_maximally_compatible(
        &self,
        states: &BTreeSet<usize>,
        groups: &[usize],
    ) -> BTreeSet<BTreeSet<usize>> {
        let alphabet = self.get_alphabet();

        let mut signatures: HashMap<Vec<Option<usize>>, BTreeSet<usize>> = HashMap::new();

        for state in states {
            let signature = alphabet
                .iter()
                .map(|c| self.move_c(*state, *c).map(|s| groups[s]))
                .collect();

            if let Some(group) = signatures.get_mut(&signature) {
                group.insert(*state);
            } else {
                signatures.insert(signature, BTreeSet::from([*state]));
            }
        }
        signatures.into_values().collect()
    }

    pub fn table_from_groups(&self, groups: &[BTreeSet<usize>]) -> Vec<Vec<(char, usize)>> {
        let alphabet: Vec<_> = self.get_alphabet().into_iter().collect();

        groups
            .iter()
            .map(|source| {
                alphabet
                    .iter()
                    .cartesian_product(groups.iter().enumerate())
                    .filter_map(|(c, (i, g))| {
                        self.move_c(*source.first().unwrap(), *c)
                            .and_then(|moved| g.contains(&moved).then_some((*c, i)))
                    })
                    .collect()
            })
            .collect()
    }
}

impl From<Vec<Vec<(char, usize)>>> for DTable {
    fn from(table: Vec<Vec<(char, usize)>>) -> Self {
        DTable(
            table
                .into_iter()
                .map(|row| row.into_iter().map(LabeledArrow::from).collect())
                .collect(),
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct DFA {
    /// Table of transitions, each row represents a state.
    table: Vec<Vec<LabeledArrow>>,
    initial_state: usize,
    final_states: BTreeSet<usize>,
}

impl DFA {
    pub fn move_c(&self, state: usize, char: char) -> Option<usize> {
        self.table[state].iter().find_map(|a| a.move_c(char))
    }

    pub fn accept(&self, input: &str) -> bool {
        let mut state = self.initial_state;
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

    #[allow(dead_code)]
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
            .flat_map(|(source, trans)| trans.iter().map(move |a| a.to_graphviz(&source)))
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
            self.initial_state,
            arrows.join("\n")
        )
    }
}

impl From<NDFA> for DFA {
    fn from(ndfa: NDFA) -> Self {
        let (table, initial_state, final_states) = ndfa.worklist();
        let table = table
            .into_iter()
            .map(|row| row.into_iter().map(LabeledArrow::from).collect())
            .collect();

        DFA {
            table,
            initial_state,
            final_states,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TaggedDFA {
    /// Table of transitions, each row represents a state.
    table: DTable,
    initial_state: usize,
    final_states: BTreeMap<usize, String>,
}

impl TaggedDFA {
    #[allow(dead_code)]
    pub fn to_graphviz(&self) -> String {
        let preamble = r#"digraph {
rankdir = LR;
ranksep = .75;
    node [shape=circle style=filled]
    start [shape=none, label="start", style=""]
"#;

        let arrows: Vec<String> = self
            .table
            .0
            .iter()
            .enumerate()
            .flat_map(|(source, trans)| trans.iter().map(move |a| a.to_graphviz(&source)))
            .collect();

        let final_states: Vec<String> = self
            .final_states
            .iter()
            .map(|(fs, tag)| format!(r##"
subgraph cluster_final_state_{} {{
	style=filled;
	fillcolor="#bfffff";
        {} [shape=doublecircle]
	label = "{}";
}}
"##, fs, fs, tag))
            .collect();

        format!(
            "{}\n{}\nstart->{}\n{}\n}}",
            preamble,
            final_states.join("\n"),
            self.initial_state,
            arrows.join("\n")
        )
    }
    pub fn num_states(&self) -> usize {
        self.table.0.len()
    }

    pub fn move_c(&self, state: usize, char: char) -> Option<usize> {
        self.table.move_c(state, char)
    }

    pub fn accept(&self, input: &str) -> Option<&str> {
        let mut state = self.initial_state;
        for char in input.chars() {
            if let Some(next) = self.move_c(state, char) {
                state = next;
            } else {
                return None;
            }
        }
        self.final_states.get(&state).map(String::as_str)
    }

    pub fn get_final_and_non_final_partition(&self) -> BTreeSet<BTreeSet<usize>> {
        let mut groups: BTreeSet<BTreeSet<usize>> = BTreeSet::new();

        for tag in self.final_states.values() {
            let tagged = self
                .final_states
                .keys()
                .filter_map(|s| (self.final_states.get(s).unwrap() == tag).then_some(*s))
                .collect();
            groups.insert(tagged);
        }

        groups.insert(
            (0..self.num_states())
                .filter(|s| !self.final_states.contains_key(s))
                .collect(),
        );
        groups
    }

    pub fn minimize(&self) -> TaggedDFA {
        let mut groups = self.get_final_and_non_final_partition();

        let mut marked: BTreeSet<BTreeSet<usize>> = BTreeSet::new();

        'outer: loop {
            let state_to_group: Vec<usize> = (0..self.num_states())
                .map(|s| {
                    groups
                        .iter()
                        .enumerate()
                        .find_map(|(i, g)| g.contains(&s).then_some(i))
                        .unwrap()
                })
                .collect();

            while let Some(g) = groups.pop_first() {
                let mut maximally_compatible_subgroups =
                    self.table.get_maximally_compatible(&g, &state_to_group);

                if maximally_compatible_subgroups.len() == 1 {
                    marked.append(&mut maximally_compatible_subgroups);
                } else {
                    groups.append(&mut maximally_compatible_subgroups);
                    groups.append(&mut marked);

                    continue 'outer;
                }
            }
            break;
        }

        let groups: Vec<BTreeSet<usize>> = marked.into_iter().collect();
        let table = self.table.table_from_groups(&groups).into();

        let mut final_states = BTreeMap::new();

        for (i, group) in groups.iter().enumerate() {
            for state in group {
                if let Some(tag) = self.final_states.get(state) {
                    final_states.insert(i, tag.to_owned());
                    break;
                }
            }
        }
        let initial_state = groups
            .iter()
            .enumerate()
            .find_map(|(i, g)| (g.contains(&self.initial_state)).then_some(i))
            .unwrap();

        TaggedDFA {
            table,
            initial_state,
            final_states,
        }
    }
}

impl From<TaggedNDFA> for TaggedDFA {
    fn from(ndfa: TaggedNDFA) -> Self {
        let (table, initial_state, final_states) = ndfa.worklist();
        let table = DTable(
            table
                .into_iter()
                .map(|row| row.into_iter().map(LabeledArrow::from).collect())
                .collect(),
        );

        TaggedDFA {
            table,
            initial_state,
            final_states,
        }
    }
}

impl From<&Lexer> for TaggedDFA {
    fn from(lexer: &Lexer) -> Self {
        let ndfa: TaggedNDFA = lexer.into();
        ndfa.into()
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::automata::ndfa::{Arrow, NDTable};

    #[test]
    fn test_basic_to_dfa() {
        let arrow = Arrow::Epsilon(1);
        let aut = NDFA {
            table: NDTable(vec![vec![arrow], vec![]]),
            initial_state: 0,
            final_state: 1,
        };

        let dfa: DFA = aut.into();
        dbg!(&dfa);

        let expected = DFA {
            table: vec![vec![]],
            initial_state: 0,
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

#[cfg(test)]
mod tests_tagged {
    use crate::{
        Lexer,
        automata::{dfa::TaggedDFA, tagged_ndfa::TaggedNDFA},
        lexer::Pattern,
    };

    #[test]
    fn tagged_from_lexer2() {
        let lex = Lexer {
            patterns: vec![
                Pattern {
                    regex: "(if)|(else)|(then)".to_string(),
                    tag: "keyword".to_string(),
                },
                Pattern {
                    regex: "(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z)+".to_string(),
                    tag: "identifier".to_string(),
                },
            ],
        };

        let tagged_ndfa: TaggedNDFA = (&lex).into();
        let tagged_dfa: TaggedDFA = tagged_ndfa.into();
        let minimized = tagged_dfa.minimize();

        assert_eq!(Some("keyword"), tagged_dfa.accept("if").as_deref());
        assert_eq!(Some("keyword"), tagged_dfa.accept("then").as_deref());
        assert_eq!(Some("keyword"), tagged_dfa.accept("else").as_deref());
        assert_eq!(Some("identifier"), tagged_dfa.accept("hola").as_deref());
        assert_eq!(Some("identifier"), tagged_dfa.accept("ifident").as_deref());
        assert_eq!(None, tagged_dfa.accept("hola1").as_deref());
        println!("{}", &minimized.to_graphviz());
        println!("{}", &tagged_dfa.to_graphviz());
        assert!(false)
    }

    #[test]
    fn minimize_tagged() {
        let lex = Lexer {
            patterns: vec![
                Pattern {
                    regex: "a*b".to_string(),
                    tag: "tag1".to_string(),
                },
                Pattern {
                    regex: "(aab|b)*".to_string(),
                    tag: "tag2".to_string(),
                },
            ],
        };

        let tagged_ndfa: TaggedNDFA = (&lex).into();
        let tagged_dfa: TaggedDFA = tagged_ndfa.into();

        let minimized = tagged_dfa.minimize();

        assert_eq!(tagged_dfa.accept("ab"), minimized.accept("ab"));
        assert_eq!(tagged_dfa.accept("aab"), minimized.accept("aab"));
        assert_eq!(
            tagged_dfa.accept("aabbbbaab"),
            minimized.accept("aabbbbaab")
        );
        assert_eq!(tagged_dfa.accept("b"), minimized.accept("b"));
        assert_eq!(tagged_dfa.accept("c"), minimized.accept("c"));
    }
}
