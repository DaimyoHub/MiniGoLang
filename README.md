# Mini-Go Compiler

As part of the CSC_52064_EP compilation course at École Polytechnique, we
implemented a compiler for a Mini-Go subset targeting the Intel x86-64
architecture. Developed incrementally on GitHub, the project was split into two
main phases: front-end semantic analysis (parsing, type checking, and symbol
resolution) and back-end assembly code generation.

A compiler for a subset of Go targeting the **Intel x86-64** architecture,
implemented in OCaml with Dune.

**Authors:** Radu-Mihai Costache & Alexis Pocquet — M1 MPRI, École Polytechnique
(IP Paris)

A detailed report of the implementation is available in `report.pdf`.

---

## Overview

The compiler is structured in two main phases:

- **Front-end** — lexing, parsing, symbol resolution, and type checking, with
structured error accumulation via a monadic `Error` module.
- **Back-end** — x86-64 assembly code generation using a stack-based
compilation scheme, preceded by a rewriting pass that simplifies the typed AST.

---

## Requirements

`ocaml`, `dune`, `gcc`, `go` — install OCaml dependencies via opam: `opam
install dune`

---

## Build

```bash
make minigo.exe
```

---

## Usage

```bash
./minigo.exe <source.go>         # Compile a Mini-Go source file
./minigo.exe --debug <source.go> # Emit debug info alongside assembly
```

The compiler outputs an x86-64 `.s` assembly file, which can then be linked
with `gcc`:

```bash
gcc -g -no-pie output.s -o output
./output
```

---

## Testing

```bash
make check
```

This runs three test groups against the compiled binary:

```
tests/test -1 ../minigo.exe   # Parsing / rejection tests
tests/test -2 ../minigo.exe   # Typing tests
tests/test -3 ../minigo.exe   # Execution tests
```

The compiler passes all provided tests. Additional tests were added to cover:

- **Nested struct access** (`tests/exec/extra_struct.go`)
- **Forward function calls** (`tests/typing/good/use-before-def.go`)
- **Mutually recursive functions** (`tests/typing/good/mutuallyrec.go`)
