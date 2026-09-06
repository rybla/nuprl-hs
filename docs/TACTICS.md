# Tactic language

Tactics are the user-facing language of refinement (NuPRL chapter 9). A
tactic is a pure function from a focused proof node to a (possibly still
incomplete) proof. Combinators are the standard LCF ones.

## Primitive tactics

| Tactic | Effect |
|--------|--------|
| `intro` | Inhabit the conclusion (λ / pair / Ax / …) |
| `intro x` | Name the bound variable |
| `intro left` / `left` | Left injection of a union / disjunction |
| `intro right` / `right` | Right injection |
| `intro with t` | Witness for Σ / ∃ / set |
| `elim N` | Eliminate hypothesis `N` |
| `elim N with t` | Instantiate a Π / ∀ hypothesis |
| `hyp` | Search hypotheses for a match |
| `hyp N` | Use hypothesis `N` |
| `eq` | Canonical equality / membership |
| `auto` | Bounded proof search |
| `auto N` | Search of depth `N` |
| `arith` | Closed integer equalities |
| `prove_prop` | Propositional tableau (via `auto`) |
| `compute` | Weak-head reduce the conclusion |
| `reduce` | Repeat `compute` |
| `D` / `D N` | Decompose clause `N` (`0` = conclusion) |
| `cut T` / `cut T as x` | Assert `T` |
| `lemma NAME` | Add a complete theorem as a hypothesis |
| `lemma NAME [t1,… ]` | Instantiate leading ∀s |
| `thin N` | Drop a hypothesis |
| `split` | Non-dependent pair / ∧ introduction |
| `exists t` | Provide an existential witness |
| `assumption` | Synonym for `hyp` |
| `idtac` | Do nothing |
| `fail` | Fail |
| `decide a = b` | Case analysis on integer equality |
| `decide a < b` | Case analysis on integer comparison |
| `decide t` | Case analysis on a union-typed term |

## Combinators

| Form | Meaning |
|------|---------|
| `t1 THEN t2` | Run `t2` on every new open goal of `t1` |
| `t1 THENL [u, v, …]` | One tactic per immediate subgoal |
| `t1 ORELSE t2` | Backtracking |
| `REPEAT t` | Apply until failure (always succeeds) |
| `TRY t` | `t ORELSE idtac` |
| `t1 ; t2` | Same as `THEN` (in tactic expressions) |

In a theory-file `proof` block, **each line is a tactic**, and lines are
composed with `THEN`.

## Automation

`auto` tries, in order, at decreasing depth:

1. `hyp` on some hypothesis
2. `eq` (canonical equality)
3. trivial `intro` (`Unit` / `True` / equality)
4. generic `intro`
5. witness-free `elim`
6. `compute`

Depth defaults to 6. It is complete enough for identity, K, and a useful
fragment of intuitionistic propositional logic, and incomplete (by design)
for goals that need a witness (`∃`, dependent pairs).

## Scripts in theory files

```
theorem identity :
  ∀A:U{i}. A → A
proof
  intro A
  intro x
  hyp
qed
```

Branching:

```
elim 5 with x THENL [hyp, elim 4 with y THENL [hyp, hyp]]
```
