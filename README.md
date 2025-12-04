# Toycomp

Realy simple toy compiler implemented in rust.

## How to use

### To compile the compiler

Since the algorithm to generate the LALR automaton for parsing is not very efficient, its necessary to precompute the automaton.

First, there should be a file named: `toycomp_lalr_automaton.bin`

```
touch toycomp_lalr_automaton.bin
```

Then compile and run the `automata_generator` binary:

```
cargo build --release --bin automata_generator
./target/release/automata_generator
```

This should replace the original `toycomp_lalr_automaton.bin` with the serialized LALR automaton.

Next, compile the main binary:

```
cargo build --release --bin compiler
```

Finally, try with the one of the examples:

```
./target/release/compiler compile --input examples/checkerboard.lang --out compiled
```

## About the implemented language

Implements an imperative statically typed language loosely based on rust syntax.

## About the target language

The target language is an intermediate representation language for a the FIS-25 virtual machine.
