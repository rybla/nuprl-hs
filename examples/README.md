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
| `choice.nuprl` | Constructive axiom of choice (independent and dependent) |
| `cps.nuprl` | CPS as double-negation translation; irrefutability of LEM |
| `existence.nuprl` | Strong vs. weak existence, squash, unique existence |
| `nd.nuprl` | Depth-indexed object logic; soundness of natural deduction |
| `listprog.nuprl` | Lists as a programming theory (Constable et al. §11.2) |
| `combinatory.nuprl` | SKI combinators and Church encodings |
| `hoare.nuprl` | Hoare triples over the streams-of-states model (§11.6) |
| `regular.nuprl` | Regular sets / Kleene algebra (Constable et al. §11.4) |
| `euclid.nuprl` | Verified Euclidean algorithm on closed integers |

Theorems are checked by replaying their `proof` scripts on the kernel. A
failing script is a check error, not a silent skip.

`stack exec build-website` renders each of these files as an annotated HTML
document under `website/examples/`.
