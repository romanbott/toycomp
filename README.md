# Toycomp

A small compiler for a toy imperative language, targeting the FIS-25 virtual machine.

## Layout

- `crates/toycomp-syntax` — reusable front-end toolkit: regular expressions,
  automata, lexer, context-free grammars and LALR(1) table construction. It
  knows nothing about the toy language.
- `crates/toycomp-lang` — the toy language itself: AST, lexer/grammar specs,
  type checker and code generator. Its `build.rs` compiles
  `spec/toy.lang.lex` and `spec/toy.lang.grammar` into Rust source tables in
  `$OUT_DIR`, so the compiler neither builds them at startup nor decodes a
  binary artifact.
- `crates/toycomp-cli` — the binaries: `compiler`, `lexgen`, `parsergen` and
  `regex-cli`.

## Build and run

```
cargo build --release
./target/release/compiler compile --input examples/checkerboard.lang --output compiled
```

`cargo build` on a fresh clone is enough. `toycomp-lang/build.rs` reruns
automatically when either spec file changes.

## Tools

```
cargo run --release --bin parsergen -- crates/toycomp-lang/spec/toy.lang.grammar --emit stats
cargo run --release --bin lexgen    -- crates/toycomp-lang/spec/toy.lang.lex --emit stats
cargo run --release --bin regex-cli -- 'a+b' 'aaab'
```

`--emit rs` prints the same `Table`/`StaticDFA` source that `build.rs`
generates, and `lexgen --emit dot` prints the minimized DFA.

`--emit bin` (bincode of the compact `TableData`/`DfaData`) is opt-in and
only exists for external consumers/debugging:

```
cargo build --release -p toycomp-cli --features bin-tables
cargo run   --release -p toycomp-cli --features bin-tables --bin parsergen -- \
    crates/toycomp-lang/spec/toy.lang.grammar --emit bin -o table.bin
```

The compiler never enables `bin-tables`, so its build has no serde/bincode
dependency.

## About the implemented language

Implements an imperative statically typed language loosely based on rust syntax.

## About the target language

The target language is an intermediate representation language for a the FIS-25 virtual machine.
