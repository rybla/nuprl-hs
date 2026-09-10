# Example theories

Each file is a self-contained `.nuprl` theory. Check one with:

```
stack exec nuprl -- check examples/logic.nuprl
```

| File | What it shows |
|------|----------------|
| `core.nuprl` | Logic encodings as named abstractions; `True` intro |
| `functions.nuprl` | Category of types and functions: composition laws, Fork/Case universal properties, currying isomorphism, extensionality |
| `logic.nuprl` | Intuitionistic predicate logic, De Morgan, quantifiers, squash |
| `equality.nuprl` | Equivalence properties, Leibniz substitution, constructor congruences, and discrimination |
| `integers.nuprl` | Discrete decidability, strict order decidability, sign splitting, and ternary integer induction |
| `lists.nuprl` | Foundational list theory: constructors, discrimination, structural recursion, Map, Append, Length, and reduction equations |
| `classical.nuprl` | DNE and stability from excluded middle |
| `cardinality.nuprl` | Equipollence, finite segments, pigeonhole (§11.3 of the Nuprl book) |
| `denotational.nuprl` | Stream-of-states model, semantic equivalence (`SemEq`), algebraic command laws, and depth-indexed syntax (§11.6) |
| `intersection.nuprl` | Family intersection `⋂x:A. B` and independent `A ∩ B` |
| `sets.nuprl` | Set types `{x:A \| P}`, subset preorder, empty/full/singleton, Nat, Positive |
| `quotients.nuprl` | Quotient types, functionality principle, `ℤ/2ℤ`, successor vs. max (§2.4, §10.3) |
| `choice.nuprl` | Constructive axiom of choice (independent and dependent) |
| `cps.nuprl` | Continuation monad, algebraic laws, Kleisli composition, and constructive double-negation embedding |
| `existence.nuprl` | Strong vs. weak existence, squash, unique existence |
| `nd.nuprl` | Depth-indexed object logic, formula validity across valuations, soundness of natural deduction |
| `listprog.nuprl` | List programming, symbol tables / environments (`EmptyEnv`, `Extend`, `Lookup`), and higher-order combinators (`Foldr`, `Filter`) |
| `combinatory.nuprl` | SKI, B, CFlip, W combinator algebra, typing and reduction laws, and polymorphic Church encodings |
| `hoare.nuprl` | Sound structural rules of Hoare logic (Skip, Pre, Post, Conjunction, Disjunction, Assignment) over stream semantics (§11.6) |
| `regular.nuprl` | Regular expressions as languages, language containment preorder, mutual equivalence, and Kleene algebra (§11.4) |
| `euclid.nuprl` | Verified Euclidean algorithm, structural step properties, common divisor specification, and coprimality |

Theorems are checked by replaying their `proof` scripts on the kernel. A
failing script is a check error, not a silent skip.

`stack exec build-website` renders each of these files as an annotated HTML
document under `website/examples/`.
