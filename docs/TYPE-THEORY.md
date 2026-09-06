# Computational type theory

nuprl-hs implements a refinement calculus for **computational type theory**
(CTT), the logic of the NuPRL Proof Development System (Constable *et al.*,
*Implementing Mathematics with the Nuprl Proof Development System*, 1986;
Jackson, *Nuprl 4.2 Reference Manual*, 1995).

## Sequents

A sequent is

```
H1, …, Hn ⊢ C
```

Each hypothesis `Hi` is a typed declaration `x : T`, possibly **hidden**
(`[x : T]`). Hidden hypotheses cannot appear in extracts; they arise from
squash and set elimination (NuPRL §9.12). Variables whose names begin with
`%` are invisible in display, matching NuPRL.

A sequent is **closed** when every free variable of a clause is bound by an
earlier declaration. The kernel only produces closed subgoals.

## Uniform terms

Every object-language expression is a uniform term (NuPRL §4.2)

```
opid{p1:k1; …; pm:km}(x1,…,xa1.t1; …; xn,…,xan.tn)
```

or a variable. Surface notation is display sugar; the kernel never depends on
it.

## Universes

Types inhabit a cumulative hierarchy `U{i}`. Level expressions are

```
L ::= v | k | L+n | max(L, L)
```

Level variables are implicitly quantified over the positive integers, so a
theorem stated at `U{i}` is valid at every universe (NuPRL §9.1.2). `P{i}` is
the propositional universe, a soft encoding of `U{i}`.

## Type formers

| Surface           | Uniform                         | Inhabitant          |
|-------------------|---------------------------------|---------------------|
| `Void`, `False`   | `void()`                        | *(none)*            |
| `Unit`, `True`    | `unit()`                        | `Ax`                |
| `Int`             | `int()`                         | numerals            |
| `Atom`            | `atom()`                        | `"tokens"`          |
| `(x:A) → B`       | `function(A; x.B)`              | `λx. b`             |
| `(x:A) × B`       | `product(A; x.B)`               | `<a, b>`            |
| `A ⊎ B`           | `union(A; B)`                   | `inl` / `inr`       |
| `a = b ∈ A`       | `equal(A; a; b)`                | `Ax`                |
| `List A`          | `list(A)`                       | `[]`, `h :: t`      |
| `{x:A \| P}`      | `set(A; x.P)`                   | a witness of `A`    |
| `[A]`             | `squash(A)`                     | `Ax`                |

Non-dependent `A → B` and `A × B` use a dummy binder.

## Logic encodings (soft)

As in NuPRL §9.1.4, the propositional connectives are *soft abstractions*:
tactics treat them as transparent.

| Surface     | Unfolds to        |
|-------------|-------------------|
| `True`      | `Unit`            |
| `False`     | `Void`            |
| `¬A`        | `A → Void`        |
| `A ∧ B`     | `A × B`           |
| `A ∨ B`     | `A ⊎ B`           |
| `A ⇒ B`     | `A → B`           |
| `A ⇔ B`     | `(A→B) × (B→A)`   |
| `∀x:A. B`   | `(x:A) → B`       |
| `∃x:A. B`   | `(x:A) × B`       |
| `t ∈ A`     | `t = t ∈ A`       |
| `P{i}`      | `U{i}`            |

## Computation

Reduction is lazy (weak-head). Canonical redexes include

- `(λx. b) a` → `b[a/x]`
- `spread(<a,b>; x,y.t)` → `t[a/x, b/y]`
- `decide(inl a; …)` / `decide(inr b; …)`
- closed integer arithmetic, `int_eq`, `less`
- `list_ind` on `[]` and `::`

The equality rule first computes both sides.

## Extracts

A complete proof determines a **realizer** (extract term). Introduction of
`A → B` extracts a λ-abstraction; elimination of `Void` extracts `any`;
equality proofs extract `Ax` (equality is proof-irrelevant). Checking a
theorem replays its tactic script on the kernel and then reads the extract
off the resulting proof tree.

## Kernel rules

Every completed proof is a tree of primitive refinements (`Nuprl.Rule`):

- `hyp N` — use a visible hypothesis
- `intro` — type-directed introduction (λ, pair, inl/inr, Ax, …)
- `elim N` — type-directed elimination (apply, spread, decide, induction, …)
- `eq` — canonical equality / membership
- `compute` — weak-head reduce the conclusion
- `cut T` — assert an intermediate type
- `lemma NAME` — copy a complete theorem into the hypotheses
- `thin N` — drop a hypothesis that is not free in the remainder

Tactics are programs that search for such trees. Soundness of a checked
theorem depends only on the kernel, not on the tactics (NuPRL §7.4).
