# Changelog for `nuprl-hs`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## 0.2.0.0

### Added

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
