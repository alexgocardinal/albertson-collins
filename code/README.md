# Reproducible cyclic tournaments

The core module `cyclic_tournaments.py` requires only Python 3.10 or later and its standard library. It constructs a directed tournament on the labelled vertices `0,...,n-1` from the rule

```
u -> v  iff  (v-u) modulo n belongs to S.
```

Here `n` must be positive and odd, and `S` contains exactly one member of each pair `{d,n-d}` for `1 <= d <= n//2`. The canonical labels are **1 on `0,...,n//2` and 2 on the remaining vertices**. These are distinguishing labels, not a proper vertex coloring.

## Commands

From the `code` directory:

```bash
python3 cyclic_tournaments.py examples
python3 cyclic_tournaments.py exhaustive --max-n 23 --output finite_check_results.json
python3 check_implementation.py
python3 cyclic_tournaments.py one 7 --connectors 1,2,4 --name my_paley7 --output ../graphs
```

For an optional PNG preview (requires `matplotlib`):

```bash
python3 plot_examples.py
```

## Work with the graphs in Python

```python
from cyclic_tournaments import CyclicTournament, automorphisms, distinguishing_report

t = CyclicTournament(9, frozenset({1, 3, 4, 7}))
print(t.arcs)
print(t.adjacency)
print(t.canonical_coloring)
print(distinguishing_report(t))
# Full automorphism group, not just translations:
full_group = list(automorphisms(t.adjacency))
colored_group = list(automorphisms(t.adjacency, t.canonical_coloring))
assert len(full_group) == 81
assert colored_group == [tuple(range(9))]
```

`automorphisms` accepts the adjacency matrix of **any** tournament, including one that is not cyclic. Its optional color vector may be arbitrary. A permutation is a tuple `p` with `p[v]` the image of vertex `v`.

The search uses stable directed color refinement, then enumerates compatible partial bijections. Every newly assigned vertex is checked against all assigned vertices in both arc directions. Refinement preserves every possible color-preserving automorphism, so this is a complete search. It does not restrict the answer to affine maps, cyclic translations, odd-order permutations, or any assumed automorphism group. A limit of 2 suffices for the distinguishing test: the identity always exists, and any second map is a counterexample. Full uncolored group enumeration can be expensive on larger examples.

## Four examples

| File stem | Order | Connector set | Full automorphism group order | Canonical-colored group order |
|---|---:|---|---:|---:|
| `c3` | 3 | `{1}` | 3 | 1 |
| `regular5` | 5 | `{1,2}` | 5 | 1 |
| `paley7` | 7 | `{1,2,4}` | 21 | 1 |
| `wreath9` | 9 | `{1,3,4,7}` | 81 | 1 |

`paley7` has nontranslation automorphisms, for example multiplication by 2 modulo 7. Thus checking translations alone would miss symmetries. `wreath9` is the lexicographic product of a directed triangle with a directed triangle. Its blocks are the residue classes modulo 3:

```
{0,3,6}, {1,4,7}, {2,5,8}.
```

The canonical half `{0,1,2,3,4}` has block intersection sizes `2,2,1`. This exhibits the quotient-and-block induction in the proof. Each block internally induces a directed triangle.

Every example is supplied as JSON (including adjacency, arcs, labels, and exact check results), arc CSV, adjacency CSV, DOT, and SVG. The PNG overview is a preview of the same exact graphs. **Arc directions matter.** Ordinary graph6 encoding would reduce each tournament to a complete undirected graph and is intentionally not used.

## Verification performed

- `finite_check_results.json`: all **4,095 labelled connector sets** at odd orders `1,3,...,23`; every canonical coloring has trivial stabilizer. At order `n`, all `2**(n//2)` choices of `S` are checked. Isomorphic tournaments with different connector sets are deliberately retained. The degenerate order-one case is an induction control; the stated tournament conjecture begins at order three.
- `implementation_check_results.json`: **2,258 independent comparisons** with a separate all-permutations oracle. This includes every tournament of orders 1 through 5, uncolored and with a two-color vector, and 30 seeded random tournaments at orders 6 and 7, uncolored and with a three-color vector. The four known full group orders and six invalid connector inputs are also checked.

These checks are finite verification and software checks. They do not establish the all-order theorem; that requires the mathematical proof and its cited permutation-group input. They are not Lean certificates.
