# nuprl-hs

A modern Haskell implementation of the **NuPRL** proof development system:
computational type theory (CTT) as a refinement theorem prover, with a tactic
language, a text-based theory library, and a complete CLI.

The original NuPRL 4.2 system (Jackson, 1995) is an X11 structured editor
driven from an ML top loop. This port keeps the *logic* — uniform terms,
sequents, primitive refinement rules, extracts, soft encodings, universe
levels — and replaces the window system with a file-based proof language
and a command-line interface. The kernel is **pure**; IO lives only at the
CLI / REPL boundary.

## Quick start

Requires [Stack](https://docs.haskellstack.org/) and GHC 9.12 (the resolver
in `stack.yaml`).

```
stack test          # 41+ staged unit tests plus example theories
stack exec nuprl -- check examples/functions.nuprl
stack exec nuprl -- extract examples/functions.nuprl identity
stack exec nuprl    # interactive REPL
```

In the REPL:

```
nuprl> load examples/logic.nuprl
nuprl> list
nuprl> prove true_is_true
prove:true_is_true> intro
prove:true_is_true> qed
nuprl> compute (λx. x) (1 + 2)
```

## Documentation

| Document | Contents |
|----------|----------|
| [docs/TYPE-THEORY.md](docs/TYPE-THEORY.md) | Sequents, type formers, computation, extracts |
| [docs/TACTICS.md](docs/TACTICS.md) | Tactic language and combinators |
| [docs/CLI.md](docs/CLI.md) | REPL, subcommands, purity boundary |
| [examples/README.md](examples/README.md) | Worked theories |
| Haddock (`stack haddock`) | Module-level API |

`nuprl help tactics` (and `terms`, `rules`, `examples`) prints a short
summary without leaving the REPL.

## Architecture

```
theory file  --parse-->  Theory
                            |
                            v
                     checkTheory          (pure)
                            |
                            v
              TacticExpr  -->  Proof tree  -->  extract
                            \                    /
                             \--> primitive rules
```

| Module | Role |
|--------|------|
| `Nuprl.Term` | Uniform terms, levels, pattern synonyms |
| `Nuprl.Subst` | Capture-avoiding substitution, α-equivalence, matching |
| `Nuprl.Parse` / `Nuprl.Pretty` | Surface syntax |
| `Nuprl.Compute` | Lazy reduction + soft unfold |
| `Nuprl.Sequent` | Hypotheses, hidden hyps, clause indices |
| `Nuprl.Rule` | **Kernel** — primitive refinement rules |
| `Nuprl.Proof` | Proof trees, addresses, extract |
| `Nuprl.Tactic` | LCF combinators, `auto`, tactic scripts |
| `Nuprl.Library` / `Nuprl.Check` | Objects, theories, replay |
| `Nuprl.Command` | Pure session / command interpreter |
| `Nuprl.REPL` / `Nuprl.CLI` | IO boundary |

A completed proof is a tree of kernel rules. Tactics search for such trees;
they are not part of the trusted computing base (NuPRL §7.4).

## Implementation stages

The test suite is grouped to match the build-up of the system, so a
regression in an early layer fails in its own group:

1. **Terms** — AST, universe levels, canonical classification
2. **Substitution** — free variables, capture avoidance, α-equivalence, matching
3. **Parse / pretty** — surface syntax, including Unicode connectives
4. **Computation** — β, arithmetic, spread, decide, list_ind, soft unfold
5. **Rules** — hyp, intro, eq, void elim, closed sequents
6. **Tactics** — identity, K, `True`, ∧, `1+1=2`, `auto`
7. **Theories** — every file in `examples/` parses and checks

## Theory files

```
theory Functions

theorem identity :
  ∀A:U{i}. A → A
proof
  intro A
  intro x
  hyp
qed
```

See `examples/` for combinators, propositional logic, equality, arithmetic,
lists, a classical fragment (DNE from excluded middle), cardinality
(equipollence and the pigeonhole principle), and denotational semantics
(streams of states, §11.6 of the Nuprl book).

## What is implemented

- Uniform CTT terms with binding and universe levels
- Dependent functions (Π), dependent pairs (Σ), disjoint union, equality,
  integers, atoms, lists, sets, squash
- Soft logic encodings (`True`, `False`, `∧`, `∨`, `⇒`, `∀`, `∃`, `∈`, …)
- Primitive refinement rules with extract combinators
- LCF tactics: `THEN`, `THENL`, `ORELSE`, `REPEAT`, `TRY`, `auto`, `arith`
- File-based theories, library objects, status (`*` complete, …)
- Interactive proof mode with undo
- Program extraction from complete proofs

## What is not (yet) a full NuPRL 4.2

The 1995 system is large (structured editors, a Lisp/ML hybrid, a rewrite
package, SupInf, RelRST, display-form objects, rule objects as data). This
implementation is a *modern kernel and CLI* covering the object logic and
the refinement loop. Deliberately out of scope for this first line:

- The X11 term/proof editor and display-form language
- User-defined primitive rules as library objects (the kernel is Haskell)
- The full rewrite / conversion package (NuPRL §9.7)
- SupInf and the original Arith decision procedure (we decide closed
  integer equalities by computation)
- Recursive types (`rec`) and quotient types

Those layers can be added against the same pure kernel.

## Website

A static site (GitHub Pages) lives in `website/`, generated by the
`build-website` executable. It precomputes the same analyses the CLI exposes
(`check`, `extract`, `compute`, `dump`, `show`) and embeds them in HTML: the
browser does no proving.

```
stack exec build-website            # writes website/
stack exec build-website -- --out /tmp/nuprl-site
```

The landing page links the GitHub repository, the Cornell PRL / NuPRL project,
and the 1986 book. The catalogue of theories is `examples.html`; each file in
`examples/` becomes an annotated document: statements and extracts first, then
expandable tactic scripts, refinement trees, and hover inspectors (uniform
syntax, unfolding, weak-head form). Colour is semantic (types, binders,
connectives, tactics, extracts, goals).

To publish on GitHub Pages, point the Pages source at the `website/` folder
(or copy it to `docs/` / a `gh-pages` branch). `.nojekyll` is written so
underscore paths are served as-is.

## Development

```
stack build
stack test
stack exec nuprl -- check examples/logic.nuprl
stack exec build-website
stack haddock --open
```

GHC options include `-Wall` and the extra warning set from the Stack
template (`-Widentities`, `-Wpartial-fields`, …). Every module has an
explicit export list.

## References

- R. L. Constable *et al.*, *Implementing Mathematics with the Nuprl Proof
  Development System*, Prentice-Hall, 1986. ([Implementing_mathematics_with_the_Nuprl.pdf](literature/Implementing_mathematics_with_the_Nuprl.pdf)).
- P. B. Jackson, *The Nuprl Proof Development System, Version 4.2:
  Reference Manual and User's Guide*, Cornell University, 1995
  ([Nuprl_Manual.pdf](literature/Nuprl_Manual.pdf)).
- P. Martin-Löf, *Intuitionistic Type Theory*, Bibliopolis, 1984. ([Intuitionistic_Type_Theory.pdf](literature/Intuitionistic_Type_Theory.pdf))
