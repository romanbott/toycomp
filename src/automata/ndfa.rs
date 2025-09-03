use std::{
    collections::{BTreeSet, VecDeque},
    usize,
};

use crate::automata::shunting_yard::{RegexToken, regex_to_atoms};

/// Represents a transition in a Non-deterministic Finite Automaton (NFA).
///
/// An `Arrow` can be either an epsilon transition (`Epsilon`), which requires no input,
/// or a labeled transition (`Labeled`), which requires a specific character to move to the next state.
#[derive(Clone, Copy, Debug)]
pub enum Arrow {
    Epsilon(usize),
    Labeled((char, usize)),
}

impl Arrow {
    fn get_label(&self) -> Option<char> {
        match self {
            Arrow::Epsilon(_) => None,
            Arrow::Labeled((c, _)) => Some(*c),
        }
    }

    /// Shifts the target state of the arrow by a given amount.
    /// This is used when combining automata to adjust state indices.
    fn move_target(&self, shift: usize) -> Arrow {
        match self {
            Arrow::Epsilon(t) => Arrow::Epsilon(t + shift),
            Arrow::Labeled((l, t)) => Arrow::Labeled((*l, t + shift)),
        }
    }

    /// Returns the target state if the arrow is an empty transition.
    fn epsilon(&self) -> Option<usize> {
        match self {
            Arrow::Epsilon(t) => Some(*t),
            Arrow::Labeled(_) => None,
        }
    }

    /// Returns the target state if the arrow is a labeled transition and the
    /// given character matches the label.
    fn accept(&self, char: &char) -> Option<usize> {
        match self {
            Arrow::Epsilon(_) => None,
            Arrow::Labeled((l, t)) => {
                if l == char {
                    Some(*t)
                } else {
                    None
                }
            }
        }
    }

    fn to_graphviz(&self, source: usize) -> String {
        match self {
            Arrow::Epsilon(target) => format!("{} -> {} [label={}]", source, target, "ε"),
            Arrow::Labeled((label, target)) => {
                format!("{} -> {} [label={}]", source, target, label)
            }
        }
    }
}

/// Represents a Non-deterministic Finite Automaton (NFA).
///
/// The automaton is defined by a table of transitions, the starting state, and the final state.
#[derive(Debug, Clone)]
pub struct NDFA {
    /// Table of transitions, each row represents a state.
    pub table: Vec<Vec<Arrow>>,
    pub starting: usize,
    pub final_state: usize,
}

/// Utility function to append the tables of two NFAs.
///
/// The states of the `right` automaton are shifted to avoid conflicts with the
/// `left` automaton's states.
fn append_nfas(left: &NDFA, right: &NDFA) -> NDFA {
    let new_table = [
        left.table.clone(),
        right
            .table
            .iter()
            .map(|row| {
                row.iter()
                    .map(|arrow| arrow.move_target(left.table.len()))
                    .collect()
            })
            .collect(),
    ]
    .concat();

    NDFA {
        table: new_table,
        starting: left.starting,
        final_state: right.final_state + left.table.len(),
    }
}

/// Applies the Kleene star operator (`*`) to an automaton.
///
/// Creates a new NFA that accepts zero or more repetitions of the language
/// accepted by the original automaton.
fn kleene(automaton: &NDFA) -> NDFA {
    let mut automaton = automaton.clone();
    let old_len = automaton.table.len();

    // Add epsilon transition from the old final state to the new final state
    automaton.table[automaton.final_state].push(Arrow::Epsilon(old_len));

    // Add epsilon transition from the new start state to the old start state
    automaton
        .table
        .push(vec![Arrow::Epsilon(automaton.starting)]);

    // Update start and final states to the new ones
    automaton.starting = old_len;
    automaton.final_state = old_len;
    automaton
}

/// Applies the positive closure operator (`+`) to an automaton.
///
/// Creates a new NFA that accepts one or more repetitions of the language
/// accepted by the original automaton.
fn positive_clousure(automaton: &NDFA) -> NDFA {
    let mut automaton = automaton.clone();

    // Add an epsilon transition from the final state back to the starting state
    automaton.table[automaton.final_state].push(Arrow::Epsilon(automaton.starting));

    automaton
}

/// Applies the optionality operator (`?`) to an automaton.
///
/// Creates a new NFA that accepts zero or one occurrence of the language
/// accepted by the original automaton.
fn optional(automaton: &NDFA) -> NDFA {
    let mut automaton = automaton.clone();

    // Add an epsilon transition from the starting state to the final state
    automaton.table[automaton.starting].push(Arrow::Epsilon(automaton.final_state));

    automaton
}

/// Applies the union operator (`|`) to two automata.
///
/// Creates a new NFA that accepts the union of the languages accepted by the
/// two original automata.
fn union(left: &NDFA, right: &NDFA) -> NDFA {
    let mut joined = append_nfas(left, right);

    let left_len = left.table.len();
    let joined_len = joined.table.len();
    joined.starting = joined_len;
    joined.final_state = joined_len + 1;

    // Add epsilon transitions from old final states to the new final state
    joined.table[joined_len - 1].push(Arrow::Epsilon(joined.final_state));
    joined.table[left.final_state].push(Arrow::Epsilon(joined.final_state));

    // Add epsilon transitions from the new start state to the old start states
    joined.table.push(vec![
        Arrow::Epsilon(left.starting),
        Arrow::Epsilon(right.starting + left_len),
    ]);

    // Add final state
    joined.table.push(vec![]);

    joined
}

/// Applies the concatenation operator to two automata.
///
/// Creates a new NFA that accepts the language formed by concatenating the
/// languages accepted by the two original automata.
fn concat(left: &NDFA, right: &NDFA) -> NDFA {
    let mut joined = append_nfas(left, right);

    // Add an epsilon transition from the first automaton's final state to the
    // second automaton's start state.
    joined.table[left.final_state].push(Arrow::Epsilon(right.starting + left.table.len()));

    joined
}

impl NDFA {
    pub fn get_alphabet(&self) -> BTreeSet<char> {
        self.table
            .iter()
            .map(|row| row.iter().filter_map(|a| a.get_label()))
            .flatten()
            .collect()
    }

    /// Creates a new NFA that accepts a single character.
    fn from_char(c: char) -> NDFA {
        NDFA {
            table: vec![vec![Arrow::Labeled((c, 1))], vec![]],
            starting: 0,
            final_state: 1,
        }
    }

    /// Creates an NFA from a regular expression string by first converting the
    /// regex to a sequence of `Atom`s using the Shunting-yard algorithm.
    pub fn from_regex(regex: &str) -> NDFA {
        NDFA::from_atoms(regex_to_atoms(regex))
    }

    /// Constructs an NFA from a sequence of `Atom`s in postfix notation.
    /// This is the core of Thompson's construction.
    // TODO: Improve error handling, remove `unwraps` and `unreachables`
    fn from_atoms(atoms: VecDeque<RegexToken>) -> NDFA {
        let mut automatons: Vec<NDFA> = vec![];

        for atom in atoms {
            match atom {
                RegexToken::Kleene => {
                    let last = automatons.pop().unwrap();
                    automatons.push(kleene(&last));
                }
                RegexToken::Concat => {
                    let first = automatons.pop().unwrap();
                    let second = automatons.pop().unwrap();
                    automatons.push(concat(&second, &first));
                }
                RegexToken::Union => {
                    let first = automatons.pop().unwrap();
                    let second = automatons.pop().unwrap();
                    automatons.push(union(&second, &first));
                }
                RegexToken::Character(c) => automatons.push(NDFA::from_char(c)),
                RegexToken::PositiveClosure => {
                    let last = automatons.pop().unwrap();
                    automatons.push(positive_clousure(&last));
                }
                RegexToken::Optional => {
                    let last = automatons.pop().unwrap();
                    automatons.push(optional(&last));
                }
                // This should not ocurr, since the Shunting Yard algorithm
                // removes parens.
                // TODO: Improve error handling
                RegexToken::OpenParen => unreachable!(),
                RegexToken::CloseParen => unreachable!(),
            }
        }

        automatons.pop().unwrap()
    }

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
        let mut unchecked: BTreeSet<usize> = BTreeSet::from_iter(states.clone().into_iter());

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

    /// Determines if the automaton accepts a given input string.
    ///
    /// The simulation proceeds by iteratively calculating the epsilon closure
    /// and then performing a character-based step for each character in the input.
    pub fn accept(&self, input: &str) -> bool {
        let mut states = BTreeSet::from([self.starting]);

        for char in input.chars() {
            states = self.epsilon_closure(&states);
            states = self.simulate_non_empty_step(&states, char);
        }
        states = self.epsilon_closure(&states);

        states.contains(&self.final_state)
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
            .map(|(source, trans)| trans.iter().map(move |a| a.to_graphviz(source)))
            .flatten()
            .collect();

        let final_state = format!("{} [shape=doublecircle]", self.final_state);

        format!(
            "{}\n{}\nstart->{}\n{}\n}}",
            preamble,
            final_state,
            self.starting,
            arrows.join("\n")
        )
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_epsilon_closure() {
        let arrow = Arrow::Epsilon(1);
        let aut = NDFA {
            table: vec![vec![arrow], vec![]],
            starting: 0,
            final_state: 1,
        };
        let ec = aut.epsilon_closure(&BTreeSet::from([0]));

        assert_eq!(BTreeSet::from([0, 1]), ec);
    }

    #[test]
    fn test_char_a() {
        let arrow = Arrow::Labeled(('a', 1));
        let aut = NDFA {
            table: vec![vec![arrow], vec![]],
            starting: 0,
            final_state: 1,
        };

        assert!(aut.accept(&"a"));
        assert!(!aut.accept(&"b"));
        assert!(!aut.accept(&"ab"));
    }

    #[test]
    fn test_ab() {
        let a_arrow = Arrow::Labeled(('a', 1));
        let b_arrow = Arrow::Labeled(('b', 2));
        let aut = NDFA {
            table: vec![vec![a_arrow], vec![b_arrow], vec![]],
            starting: 0,
            final_state: 2,
        };

        assert!(!aut.accept(&"a"));
        assert!(!aut.accept(&"b"));
        assert!(aut.accept(&"ab"));
    }

    #[test]
    fn test_concat() {
        let a_arrow = Arrow::Labeled(('a', 1));
        let b_arrow = Arrow::Labeled(('b', 1));
        let aut1 = NDFA {
            table: vec![vec![a_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };
        let aut2 = NDFA {
            table: vec![vec![b_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };

        let aut = concat(&aut1, &aut2);

        assert!(!aut.accept(&"a"));
        assert!(!aut.accept(&"b"));
        assert!(aut.accept(&"ab"));
    }

    #[test]
    fn test_or() {
        let a_arrow = Arrow::Labeled(('a', 1));
        let b_arrow = Arrow::Labeled(('b', 1));
        let aut1 = NDFA {
            table: vec![vec![a_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };
        let aut2 = NDFA {
            table: vec![vec![b_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };

        let aut = union(&aut1, &aut2);

        dbg!(&aut);

        assert!(aut.accept(&"a"));
        assert!(aut.accept(&"b"));
        assert!(!aut.accept(&"ab"));
        assert!(!aut.accept(&"c"));
    }

    #[test]
    fn single_char() {
        let a = NDFA::from_char('a');
        let b = NDFA::from_char('b');

        assert!(a.accept("a"));
        assert!(!a.accept("b"));
        assert!(!b.accept("a"));
        assert!(b.accept("b"));
    }

    #[test]
    fn concat_and_or() {
        let a = NDFA::from_char('a');
        let b = NDFA::from_char('b');
        let c = NDFA::from_char('c');

        let ab = concat(&a, &b);

        let ab_or_c = union(&ab, &c);

        assert!(ab.accept("ab"));
        assert!(ab_or_c.accept("ab"));
        assert!(ab_or_c.accept("c"));
    }

    #[test]
    fn multi_concat() {
        let a = NDFA::from_char('a');

        let mut aut = NDFA {
            table: vec![],
            starting: 0,
            final_state: 0,
        };
        for _ in 0..5 {
            aut = concat(&aut, &a);
        }

        assert!(aut.accept("aaaaa"));
        assert!(!aut.accept("aaaa"));
        assert!(!aut.accept("aaaaaa"));
    }

    #[test]
    fn test_kleene() {
        let a = NDFA::from_char('a');

        let a_kleene = kleene(&a);

        assert!(a_kleene.accept(""));
        assert!(a_kleene.accept("a"));
        assert!(a_kleene.accept("aa"));
        assert!(a_kleene.accept("aaaaaaa"));
        assert!(!a_kleene.accept("ab"));
    }

    #[test]
    fn test_positive_clousure() {
        let a = NDFA::from_char('a');

        let aut = positive_clousure(&a);

        assert!(!aut.accept(""));
        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
        assert!(aut.accept("aaaaaaa"));
        assert!(!aut.accept("ab"));
    }

    #[test]
    fn test_zero_or_one() {
        let a = NDFA::from_char('a');

        let aut = optional(&a);

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(!aut.accept("aa"));
        assert!(!aut.accept("aaaaaaa"));
        assert!(!aut.accept("ab"));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_automaton_from_atoms() {
        let aut = NDFA::from_atoms(regex_to_atoms("a*|b"));

        assert!(aut.accept(""));
        assert!(aut.accept("b"));
        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
    }

    #[test]
    fn test_automaton_from_regex() {
        let aut = NDFA::from_regex("((a*|b)c)*");

        assert!(aut.accept(""));
        assert!(aut.accept("bc"));
        assert!(aut.accept("aaaac"));
        assert!(aut.accept("aaaacbc"));
        assert!(!aut.accept("aa"));
    }
}

#[cfg(test)]
mod tests_adrian {

    use super::*;

    #[test]
    fn test_plus() {
        let aut = NDFA::from_regex("a+");

        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
        assert!(aut.accept("aaaa"));
        assert!(!aut.accept(""));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_optional() {
        let aut = NDFA::from_regex("a?");

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(!aut.accept("aa"));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_union() {
        let aut = NDFA::from_regex("a|b");

        assert!(aut.accept("a"));
        assert!(aut.accept("b"));
        assert!(!aut.accept(""));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ab"));
    }

    #[test]
    fn test_precedence_concat_over_union() {
        let aut = NDFA::from_regex("ab|c");

        assert!(aut.accept("ab"));
        assert!(aut.accept("c"));
        assert!(!aut.accept("a"));
        assert!(!aut.accept("b"));
        assert!(!aut.accept("ac"));
    }

    #[test]
    fn test_precedence_kleen_over_concat() {
        let aut = NDFA::from_regex("ab*c");

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
        let aut = NDFA::from_regex("(a|b)*");

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
        let aut = NDFA::from_regex("a(b|c)d");

        assert!(aut.accept("abd"));
        assert!(aut.accept("acd"));
        assert!(!aut.accept("ad"));
        assert!(!aut.accept("abcd"));
        assert!(!aut.accept("abd d"));
    }

    #[test]
    fn test_complex_nesting() {
        let aut = NDFA::from_regex("a(b*|c+)?d");

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
        let aut = NDFA::from_regex("(a*)*");

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_optional_inside_concat() {
        let aut = NDFA::from_regex("a(b?)c");

        assert!(aut.accept("ac"));
        assert!(aut.accept("abc"));
        assert!(!aut.accept("a"));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ab"));
        assert!(!aut.accept("bc"));
    }

    #[test]
    fn test_contains_at_least_one_a() {
        let aut = NDFA::from_regex("(a|b)*a(a|b)*");

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
