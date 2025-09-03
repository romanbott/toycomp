use std::collections::VecDeque;

/// Represents a token in a regular expression.
///
/// This enum includes literal characters and all supported operators.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum RegexToken {
    /// The Kleene star operator (`*`), for zero or more repetitions.
    Kleene,
    /// The positive closure operator (`+`), for one or more repetitions.
    PositiveClosure,
    /// The optionality operator (`?`), for zero or one repetition.
    Optional,
    /// The concatenation operator (implicitly added), for joining expressions.
    Concat,
    /// The union operator (`|`).
    Union,
    /// An opening parenthesis (`(`).
    OpenParen,
    /// A closing parenthesis (`)`).
    CloseParen,
    /// A literal character.
    Character(char),
}

impl RegexToken {
    /// Checks if the token is an operator.
    fn is_operator(&self) -> bool {
        !matches!(self, RegexToken::Character(_))
    }

    /// Returns the precedence of an operator. Higher numbers mean higher precedence.
    /// This is crucial for the Shunting-yard algorithm.
    fn precedence(&self) -> u8 {
        match self {
            RegexToken::Kleene => 8,
            RegexToken::PositiveClosure => 8,
            RegexToken::Optional => 8,
            RegexToken::Concat => 7,
            RegexToken::Union => 6,
            RegexToken::OpenParen => 5,
            RegexToken::CloseParen => 5,
            RegexToken::Character(_) => 0,
        }
    }
}

/// Converts a character into its corresponding `RegexToken` representation.
impl From<&char> for RegexToken {
    fn from(value: &char) -> Self {
        match value {
            '*' => RegexToken::Kleene,
            '+' => RegexToken::PositiveClosure,
            '?' => RegexToken::Optional,
            '|' => RegexToken::Union,
            '(' => RegexToken::OpenParen,
            ')' => RegexToken::CloseParen,
            c => RegexToken::Character(*c),
        }
    }
}

const OPERATORS: [char; 6] = ['*', '+', '?', '|', '(', ')'];
const UNARY_OPERATORS: [char; 3] = ['*', '+', '?'];

/// Checks if a character is a regex operator.
fn is_operator(input: &char) -> bool {
    OPERATORS.contains(input)
}

/// Checks if a character is a unary operator (applies to a single preceding operand).
fn is_unary(input: &char) -> bool {
    UNARY_OPERATORS.contains(input)
}

/// Inserts explicit concatenation operators into the regular expression.
///
/// This is a preprocessing step for the Shunting-yard algorithm, which
/// expects all operators to be explicitly present.
fn explicit_concat(input: &str) -> Vec<RegexToken> {
    let mut chars = input.chars().peekable();
    let mut output: Vec<RegexToken> = Vec::new();

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
                output.push(RegexToken::Concat);
            }
        }
    }

    output
}

/// Implements the Shunting-yard algorithm to convert infix to postfix (RPN).
#[derive(Debug)]
struct ShuntingYard {
    /// The queue of `RegexToken`s to be processed.
    input: VecDeque<RegexToken>,
    /// The queue to store the resulting RPN expression.
    output: VecDeque<RegexToken>,
    /// The stack used to temporarily hold operators.
    operator_stack: Vec<RegexToken>,
}

impl ShuntingYard {
    /// Initializes a new `ShuntingYard` instance from a regular expression string.
    fn new(input: &str) -> ShuntingYard {
        ShuntingYard {
            input: explicit_concat(input).into(),
            output: VecDeque::new(),
            operator_stack: vec![],
        }
    }

    /// Processes the next token from the input queue.
    fn consume_next(&mut self) {
        let current = self.input.pop_front().unwrap();

        if current.is_operator() {
            self.process_operator(current)
        } else {
            self.output.push_back(current);
        }
    }

    /// Handles the logic for processing an operator, based on its precedence
    /// and the state of the operator stack.
    fn process_operator(&mut self, current: RegexToken) {
        match &current {
            RegexToken::OpenParen => self.operator_stack.push(current),
            RegexToken::CloseParen => {
                while let Some(a) = self.operator_stack.pop() {
                    if matches!(a, RegexToken::OpenParen) {
                        break;
                    } else {
                        self.output.push_back(a);
                    }
                }
            }
            RegexToken::Character(_) => {
                unreachable!("There should not be Character's in the operator stack")
            }
            current => {
                while let Some(a) = self.operator_stack.pop() {
                    if matches!(a, RegexToken::OpenParen) {
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

    /// Converts the input regular expression into RPN.
    fn to_rpn(&mut self) {
        while !self.input.is_empty() {
            self.consume_next();
        }
        while let Some(operator) = self.operator_stack.pop() {
            self.output.push_back(operator);

        }
    }
}

/// Public function to convert a regular expression string to a deque of `RegexToken`s in RPN.
pub fn regex_to_atoms(regex: &str) -> VecDeque<RegexToken> {
    let mut st = ShuntingYard::new(regex);
    st.to_rpn();
    st.output
}

/// Unit tests for the Shunting-yard algorithm implementation.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_or() {
        let input = "a|b";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Union,
            RegexToken::Character('b'),
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }
    #[test]
    fn test_basic_concat() {
        let input = "ab";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Concat,
            RegexToken::Character('b'),
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_basic_concat_after_unary() {
        let input = "ab*c";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Concat,
            RegexToken::Character('b'),
            RegexToken::Kleene,
            RegexToken::Concat,
            RegexToken::Character('c'),
        ];

        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parens() {
        let input = "(a)(b)";
        let expected = vec![
            RegexToken::OpenParen,
            RegexToken::Character('a'),
            RegexToken::CloseParen,
            RegexToken::Concat,
            RegexToken::OpenParen,
            RegexToken::Character('b'),
            RegexToken::CloseParen,
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parens_after_unary() {
        let input = "a*(b)";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Kleene,
            RegexToken::Concat,
            RegexToken::OpenParen,
            RegexToken::Character('b'),
            RegexToken::CloseParen,
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_char_after_kleen() {
        let input = "a*b";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Kleene,
            RegexToken::Concat,
            RegexToken::Character('b'),
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_sy1() {
        let input = "a*|b";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Kleene,
            RegexToken::Character('b'),
            RegexToken::Union,
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
            RegexToken::Character('a'),
            RegexToken::Kleene,
            RegexToken::Character('c'),
            RegexToken::Concat,
            RegexToken::Character('b'),
            RegexToken::Union,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        assert_eq!(st.output, expected);
    }

    #[test]
    fn test_sy3() {
        let input = "a*(c|b)";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Kleene,
            RegexToken::Character('c'),
            RegexToken::Character('b'),
            RegexToken::Union,
            RegexToken::Concat,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        assert_eq!(st.output, expected);
    }

    #[test]
    fn test_sy4() {
        let input = "(a*)(c|b)";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Kleene,
            RegexToken::Character('c'),
            RegexToken::Character('b'),
            RegexToken::Union,
            RegexToken::Concat,
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
            RegexToken::Character('a'),
            RegexToken::Character('b'),
            RegexToken::Kleene,
            RegexToken::Concat,
            RegexToken::Character('c'),
            RegexToken::Concat,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        assert_eq!(st.output, expected);
    }

    #[test]
    fn test_sy6() {
        let input = "a(b|c)d";
        let expected = vec![
            RegexToken::Character('a'),
            RegexToken::Character('b'),
            RegexToken::Character('c'),
            RegexToken::Union,
            RegexToken::Concat,
            RegexToken::Character('d'),
            RegexToken::Concat,
        ];
        let mut st = ShuntingYard::new(input);
        st.to_rpn();
        assert_eq!(st.output, expected);
    }
}
