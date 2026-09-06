# Example theories

Each file is a self-contained `.nuprl` theory. Check one with:

```
stack exec nuprl -- check examples/logic.nuprl
```

| File | What it shows |
|------|----------------|
| `core.nuprl` | Logic encodings as named abstractions; `True` intro |
| `functions.nuprl` | Combinators, products, coproducts, η, universes, intersection |
| `logic.nuprl` | Intuitionistic predicate logic, De Morgan, quantifiers, squash |
| `equality.nuprl` | Symmetry, transitivity, Leibniz, atoms, constructor clash |
| `integers.nuprl` | Arithmetic, `<`, decidability, `ind` |
| `lists.nuprl` | Cons, recursor, `list_ind`, append |
| `classical.nuprl` | DNE and stability from excluded middle |
| `cardinality.nuprl` | Equipollence, finite segments, pigeonhole (§11.3 of the Nuprl book) |
| `denotational.nuprl` | Streams of states, Abort/Skip/Assign/Concat/IF, depth-indexed syntax (§11.6) |
| `intersection.nuprl` | Family intersection `⋂x:A. B` and independent `A ∩ B` |
| `sets.nuprl` | Set types `{x:A \| P}`, empty/full/singleton, Nat, Positive |
| `quotients.nuprl` | Quotient types, `ℤ/2ℤ`, successor vs. max (§2.4, §10.3) |

Theorems are checked by replaying their `proof` scripts on the kernel. A
failing script is a check error, not a silent skip.

`stack exec build-website` renders each of these files as an annotated HTML
document under `website/examples/`.
