# Example theories

Each file is a self-contained `.nuprl` theory. Check one with:

```
stack exec nuprl -- check examples/logic.nuprl
```

| File | What it shows |
|------|----------------|
| `core.nuprl` | Logic encodings as named abstractions; `True` intro |
| `functions.nuprl` | Identity, K, composition (extracts are λ-terms) |
| `logic.nuprl` | Intuitionistic tautologies: ∧, ∨, ⇒, *ex falso* |
| `equality.nuprl` | Membership and reflexivity |
| `integers.nuprl` | Closed arithmetic by computation |
| `lists.nuprl` | `[] ∈ List A` |
| `classical.nuprl` | `A → ¬¬A`, and DNE from excluded middle |

Theorems are checked by replaying their `proof` scripts on the kernel. A
failing script is a check error, not a silent skip.
