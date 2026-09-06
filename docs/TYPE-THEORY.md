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
squash and set elimination, and from intersection introduction
(NuPRL §9.12). Variables whose names begin with `%` are invisible in
display, matching NuPRL.

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
| `(x,y):A // E`    | `quotient(A; x,y.E)`            | a witness of `A`    |
| `A // E`          | `quotient(A; _,_.E)`            | a witness of `A`    |
| `⋂x:A. B`         | `isect(A; x.B)`                 | a common realizer of every `B[a]` |
| `A ∩ B`           | `isect(A; _.B)`                 | a realizer of `B` (independent case) |
| `[A]`             | `squash(A)`                     | `Ax` (`[t]` with no comma; `[a, b]` is a list) |
| `a < b`           | `less_than(a; b)`               | `Ax` (when `a < b`) |

Non-dependent `A → B` and `A × B` use a dummy binder. Independent
intersection `A ∩ B` is the dummy-binder case of `isect`: a term inhabits it
when it inhabits `B` for every (non-computational) index of type `A`. This is
not the set of common elements of `A` and `B`; write `{x:A | x ∈ B}` for that.

Quotient types `(x,y):A // E` (NuPRL §2.4, §8.3, §10.3) have the same
members as `A`, but `a = b ∈ A // E` when `E[a,b]` is inhabited. Formation
requires `E` to be an equivalence relation on `A`. A function out of a
quotient is well-defined only if it respects `E`.

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
- closed comparisons `n < m` compute to `Unit` or `Void`
- `list_ind` on `[]` and `::`
- `ind(n; x,ih.down; base; y,jh.up)` integer induction (0, positive, negative)

The equality rule first computes both sides.

## Extracts

A complete proof determines a **realizer** (extract term). Introduction of
`A → B` extracts a λ-abstraction; introduction of `⋂x:A. B` extracts the
realizer of `B` (the index is hidden and does not appear in the extract);
elimination of `Void` extracts `any`; equality proofs extract `Ax` (equality
is proof-irrelevant). Checking a theorem replays its tactic script on the
kernel and then reads the extract off the resulting proof tree.

## Kernel rules

Every completed proof is a tree of primitive refinements (`Nuprl.Rule`):

- `hyp N` — use a visible hypothesis
- `intro` — type-directed introduction (λ, pair, inl/inr, Ax, intersection, …)
- `elim N` — type-directed elimination (apply, spread, decide, induction, intersection instantiation, quotient functionality, …)
- `eq` — canonical equality / membership (including set, intersection, and quotient membership, and application congruence)
- `compute` — weak-head reduce the conclusion
- `cut T` — assert an intermediate type
- `lemma NAME` — copy a complete theorem into the hypotheses
- `thin N` — drop a hypothesis that is not free in the remainder
- `decide a = b` — integer equality is decidable
- `decide t` — case analysis on a union-typed term

Tactics are programs that search for such trees. Soundness of a checked
theorem depends only on the kernel, not on the tactics (NuPRL §7.4).
