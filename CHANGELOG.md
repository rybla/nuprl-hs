# Changelog for `nuprl-hs`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

## 0.1.0.0 - 2026-09-06

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
