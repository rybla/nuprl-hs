# Command-line interface

The executable is named `nuprl`. With no arguments it starts an interactive
REPL. Subcommands cover batch checking and one-shot evaluation.

## Installation

From the project root (requires [Stack](https://docs.haskellstack.org/)):

```
stack build
stack exec nuprl -- --help
```

## Subcommands

| Command | Meaning |
|---------|---------|
| `nuprl` / `nuprl repl` | Interactive REPL |
| `nuprl check FILE…` | Load and check theory files |
| `nuprl list [FILE…]` | List library objects |
| `nuprl show FILE NAME` | Show a named object |
| `nuprl extract FILE NAME` | Print a theorem's extract |
| `nuprl eval TERM` | Pretty-print a term |
| `nuprl compute TERM` | Normalize a term |
| `nuprl dump TERM` | Uniform syntax |
| `nuprl help [topic]` | Help (`tactics`, `terms`, `rules`, `examples`) |

## REPL

```
nuprl> help
nuprl> load examples/functions.nuprl
nuprl> list
nuprl> show identity
nuprl> extract identity
nuprl> prove identity
prove:identity> goals
prove:identity> intro A
prove:identity> intro x
prove:identity> hyp
prove:identity> qed
nuprl> compute (λx. x) 3
nuprl> quit
```

Top-level commands: `help`, `load`, `list`, `show`, `check`, `prove`,
`extract`, `eval`, `compute`, `dump`, `quit`.

Proof-mode commands are tactic scripts (see [TACTICS.md](TACTICS.md)) plus
`goals`, `undo`, `abort`, and `qed`.

History is stored in `.nuprl_history`. Tab completion offers command names.

## Static website

`stack exec build-website` writes a GitHub Pages site to `website/`. Example
theories are checked with the same kernel as `nuprl check`; extracts, uniform
dumps, and weak-head forms are precomputed and embedded in the HTML. See the
README for the colour key and deploy notes.

## Exit status

Batch commands (`check`, `extract`, `eval`, …) exit `0` on success and `1`
when a parse, refinement, or tactic error is reported.

## Purity

The prover, checker, and command interpreter (`Nuprl.Command.execCommand`)
are pure. The only IO in the system is:

- reading theory files
- the Haskeline REPL
- writing to stdout / stderr
