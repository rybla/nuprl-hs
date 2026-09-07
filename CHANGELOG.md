# Changelog for `nuprl-hs`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## 0.4.0.0

### Added

- Example theories: constructive axiom of choice (`choice.nuprl`), CPS as
  double-negation translation (`cps.nuprl`), weak vs. strong existence
  (`existence.nuprl`), depth-indexed natural deduction (`nd.nuprl`), lists as
  a programming theory (`listprog.nuprl`, Constable et al. §11.2), combinatory
  logic and Church encodings (`combinatory.nuprl`), Hoare logic over streams
  of states (`hoare.nuprl`), regular sets / Kleene algebra (`regular.nuprl`,
  §11.4), and a verified Euclidean algorithm (`euclid.nuprl`).

### Fixed

- Type equality uses computational conversion, so `P (Fst(<u,v>))` converts
  with `P u`.
- Dependent pair (and union) elimination substitutes `<u,v>` (resp. `inl` /
  `inr`) in the conclusion, matching list/integer induction.
- Function elimination remembers `f t` as the new hypothesis, so projections
  of a Σ-result can be reduced.
- Squash elimination is allowed on squash-stable conclusions (NuPRL §9.12).
- `P` and `U` as variables are no longer stolen by `P{i}` / `U{i}` parsers.
- `λ` is not an identifier character, so `n (λx. t)` is application.
- `cut T as x` no longer parses `as` as an applied variable.

## 0.3.0.0

### Added

- Standard-library example theories: combinators and type formers
  (`functions.nuprl`), intuitionistic logic and squash (`logic.nuprl`),
  equality / atoms (`equality.nuprl`), integer arithmetic and induction
  (`integers.nuprl`), lists (`lists.nuprl`), classical reasoning from
  excluded middle (`classical.nuprl`), and set types (`sets.nuprl`).
- Bracket syntax: `[T]` is squash, `[]` is nil, `[a, b, …]` is a list.
- Infix remainder `%` and prefix integer negation.
- Quotient types `(x,y):A // E` (`quotient`): formation (equivalence
  laws), introduction of a representative, equality via the relation,
  and functionality elimination.
- Example theory `examples/quotients.nuprl` (integers modulo 2).

## 0.2.0.0

### Added

- Intersection types `⋂x:A. B` / `A ∩ B` (`isect`): introduction (hidden
  index), elimination at a witness of the index, and equality / formation.
- Example theory `examples/intersection.nuprl`.
- Integer less-than as a type (`a < b`); closed instances compute to
  `Unit` / `Void`.
- Set-membership, application congruence, and constructor discrimination
  in the equality / elimination rules.
- `decide a = b` (decidable integer equality) and `decide t` (cases on a
  union).
- Library abstractions unfold in the refiner.
- Example theory `examples/cardinality.nuprl` (Constable et al. §11.3).
- Integer induction term `ind(n; x,ih.down; base; y,jh.up)` and `decide a < b`.
- Example theory `examples/denotational.nuprl` (Constable et al. §11.6).
- `build-website` executable: static GitHub Pages site in `website/`, with
  annotated, interactive HTML for every example theory.

## 0.1.0.0

### Added

- Computational type theory kernel: uniform terms, sequents, primitive
  refinement rules, extracts.
- Capture-avoiding substitution, α-equivalence, and first-order matching.
- Lazy computation (β, arithmetic, spread, decide, list induction) and
  soft unfold of the standard logic encodings.
- LCF tactic language (`THEN`, `THENL`, `ORELSE`, `REPEAT`, `TRY`, `auto`,
  `arith`, `intro`, `elim`, `hyp`, `eq`, …).
- Text-based theory files (`.nuprl`) and a pure checker that replays
  tactic scripts.
- CLI (`nuprl`) with REPL, `check`, `extract`, `eval`, `compute`.
- Example theories under `examples/`.
- Tasty test suite organised by implementation stage.
