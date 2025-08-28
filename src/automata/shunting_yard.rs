use std::collections::VecDeque;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Atom {
    Kleene,
    Plus,
    Question,
    Concat,
    Or,
    OpenParen,
    CloseParen,
    Character(char),
}

impl Atom {
    fn is_operator(&self) -> bool {
        !matches!(self, Atom::Character(_))
    }

    fn precedence(&self) -> u8 {
        match self {
            Atom::Kleene => 8,
            Atom::Plus => 8,
            Atom::Question => 8,
            Atom::Concat => 7,
            Atom::Or => 6,
            Atom::OpenParen => 5,
            Atom::CloseParen => 5,
            Atom::Character(_) => 5,
        }
    }
}

impl From<&char> for Atom {
    fn from(value: &char) -> Self {
        match value {
            '*' => Atom::Kleene,
            '+' => Atom::Plus,
            '?' => Atom::Question,
            '|' => Atom::Or,
            '(' => Atom::OpenParen,
            ')' => Atom::CloseParen,
            c => Atom::Character(*c),
        }
    }
}

const OPERATORS: [char; 6] = ['*', '+', '?', '|', '(', ')'];
const UNARY_OPERATORS: [char; 3] = ['*', '+', '?'];

fn is_operator(input: &char) -> bool {
    OPERATORS.contains(input)
}

fn is_unary(input: &char) -> bool {
    UNARY_OPERATORS.contains(input)
}

fn explicit_concat(input: &str) -> Vec<Atom> {
    let mut chars = input.chars().peekable();
    let mut output: Vec<Atom> = Vec::new();

    while let Some(current_char) = chars.next() {
        output.push((&current_char).into());

        // TODO; refactor
        if let Some(&next_char) = chars.peek() {
            let should_insert_concat =
                // Case 1: Concatenation of two non-operators (e.g., "ab")
                (!is_operator(&current_char) && !is_operator(&next_char))
                // Case 2: Concatenation after a closing parenthesis (e.g., "(a)b")
                || (current_char == ')' && !is_operator(&next_char))
                // Case 3: Concatenation after a unary operator (e.g., "a*b")
                || (is_unary(&current_char) && !is_operator(&next_char))
                // Case 4: Concatenation of a closing parenthesis and an opening parenthesis (e.g., "(a)(b)")
                || (current_char == ')' && next_char == '(')
                // Case 5: Concatenation of a unary operator and an opening parenthesis (e.g., "a*(b)")
                || (is_unary(&current_char) && next_char == '(')
                // Case 6: Concatenation of a not operator and an opening parenthesis (e.g., "a*(b)")
                || (!is_operator(&current_char) && next_char == '(');

            if should_insert_concat {
                output.push(Atom::Concat);
            }
        }
    }

    output
}

#[derive(Debug)]
struct ShuntingYard {
    input: VecDeque<Atom>,
    output: VecDeque<Atom>,
    operator_stack: Vec<Atom>,
}

impl ShuntingYard {
    fn new(input: &str) -> ShuntingYard {
        ShuntingYard {
            input: explicit_concat(input).into(),
            output: VecDeque::new(),
            operator_stack: vec![],
        }
    }

    fn consume_next(&mut self) {
        let current = self.input.pop_front().unwrap();

        if current.is_operator() {
            self.process_operator(current)
        } else {
            self.output.push_back(current);
        }
    }

    fn process_operator(&mut self, current: Atom) {
        match &current {
            Atom::OpenParen => self.operator_stack.push(current),
            Atom::CloseParen => {
                while let Some(a) = self.operator_stack.pop() {
                    if matches!(a, Atom::OpenParen) {
                        break;
                    } else {
                        self.output.push_back(a);
                    }
                }
            }
            Atom::Character(_) => {
                unreachable!("There should not be Character's in the opreator stack")
            }
            current => {
                while let Some(a) = self.operator_stack.pop() {
                    if matches!(a, Atom::OpenParen) {
                        self.operator_stack.push(a);
                        self.operator_stack.push(*current);
                        break;
                    } else if a.precedence() >= current.precedence() {
                        self.output.push_back(a);
                    } else {
                        self.operator_stack.push(a);
                        self.operator_stack.push(*current);
                        break;
                    }
                }
                if self.operator_stack.is_empty() {
                    self.operator_stack.push(*current);
                }
            }
        }
    }

    fn to_rpn(&mut self) {
        while !self.input.is_empty() {
            dbg!(&self);
            self.consume_next();
        }
        while !self.operator_stack.is_empty() {
            self.output.push_back(self.operator_stack.pop().unwrap());
        }
    }
}

pub fn regex_to_atoms(regex: &str) -> VecDeque<Atom> {
    let mut st = ShuntingYard::new(regex);
    st.to_rpn();
    st.output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_or() {
        let input = "a|b";
        let expected = vec![Atom::Character('a'), Atom::Or, Atom::Character('b')];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }
    #[test]
    fn test_basic_concat() {
        let input = "ab";
        let expected = vec![Atom::Character('a'), Atom::Concat, Atom::Character('b')];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_basic_concat_after_unary() {
        let input = "ab*c";
        let expected = vec![
            Atom::Character('a'),
            Atom::Concat,
            Atom::Character('b'),
            Atom::Kleene,
            Atom::Concat,
            Atom::Character('c'),
        ];

        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parens() {
        let input = "(a)(b)";
        let expected = vec![
            Atom::OpenParen,
            Atom::Character('a'),
            Atom::CloseParen,
            Atom::Concat,
            Atom::OpenParen,
            Atom::Character('b'),
            Atom::CloseParen,
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parens_after_unary() {
        let input = "a*(b)";
        let expected = vec![
            Atom::Character('a'),
            Atom::Kleene,
            Atom::Concat,
            Atom::OpenParen,
            Atom::Character('b'),
            Atom::CloseParen,
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_char_after_kleen() {
        let input = "a*b";
        let expected = vec![
            Atom::Character('a'),
            Atom::Kleene,
            Atom::Concat,
            Atom::Character('b'),
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_sy1() {
        let input = "a*|b";
        let expected = vec![
            Atom::Character('a'),
            Atom::Kleene,
            Atom::Character('b'),
            Atom::Or,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        let result = st.output;
        assert_eq!(result, expected);
    }

    #[test]
    fn test_sy2() {
        let input = "a*c|b";
        let expected = vec![
            Atom::Character('a'),
            Atom::Kleene,
            Atom::Character('c'),
            Atom::Concat,
            Atom::Character('b'),
            Atom::Or,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        assert_eq!(st.output, expected);
    }

    #[test]
    fn test_sy3() {
        let input = "a*(c|b)";
        let expected = vec![
            Atom::Character('a'),
            Atom::Kleene,
            Atom::Character('c'),
            Atom::Character('b'),
            Atom::Or,
            Atom::Concat,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        assert_eq!(st.output, expected);
    }

    #[test]
    fn test_sy4() {
        let input = "(a*)(c|b)";
        let expected = vec![
            Atom::Character('a'),
            Atom::Kleene,
            Atom::Character('c'),
            Atom::Character('b'),
            Atom::Or,
            Atom::Concat,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        let result = st.output;
        assert_eq!(result, expected);
    }

    #[test]
    fn test_sy5() {
        let input = "ab*c";
        let expected = vec![
            Atom::Character('a'),
            Atom::Character('b'),
            Atom::Kleene,
            Atom::Concat,
            Atom::Character('c'),
            Atom::Concat,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        assert_eq!(st.output, expected);
    }

    #[test]
    fn test_sy6() {
        let input = "a(b|c)d";
        let expected = vec![
            Atom::Character('a'),
            Atom::Character('b'),
            Atom::Character('c'),
            Atom::Or,
            Atom::Concat,
            Atom::Character('d'),
            Atom::Concat,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        assert_eq!(st.output, expected);
    }
}
