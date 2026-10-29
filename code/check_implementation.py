#!/usr/bin/env python3
"""Independent finite oracle comparisons for the exact automorphism engine."""
from __future__ import annotations

from itertools import combinations, permutations
import json
from pathlib import Path
import random
from cyclic_tournaments import CyclicTournament, automorphisms, distinguishing_report


def naive_permutations(a, colors):
    """No refinement or backtracking: test each permutation directly."""
    n = len(a)
    answer = set()
    for p in permutations(range(n)):
        if any(colors[v] != colors[p[v]] for v in range(n)):
            continue
        if all(a[u][v] == a[p[u]][p[v]] for u in range(n) for v in range(n)):
            answer.add(p)
    return answer


def matrix(n, bits):
    a = [[0] * n for _ in range(n)]
    for i, (u, v) in enumerate(combinations(range(n), 2)):
        a[u][v] = (bits >> i) & 1
        a[v][u] = 1-a[u][v]
    return a


def compare(a, colors):
    expected = naive_permutations(a, colors)
    observed = set(automorphisms(a, colors))
    assert observed == expected, {"a": a, "colors": colors,
                                  "expected": sorted(expected), "observed": sorted(observed)}


def main():
    comparisons = 0
    for n in range(1, 6):
        for bits in range(1 << (n*(n-1)//2)):
            a = matrix(n, bits)
            for colors in [(0,)*n, tuple(v <= n//2 for v in range(n))]:
                compare(a, colors)
                comparisons += 1
    rng = random.Random(20261028)
    for n, count in [(6,20), (7,10)]:
        for _ in range(count):
            a = matrix(n, rng.randrange(1 << (n*(n-1)//2)))
            for colors in [(0,)*n, tuple(rng.randrange(3) for _ in range(n))]:
                compare(a, colors)
                comparisons += 1
    examples = [(3,{1},3), (5,{1,2},5), (7,{1,2,4},21), (9,{1,3,4,7},81)]
    for n, s, expected_order in examples:
        t = CyclicTournament(n, frozenset(s))
        assert len(t.arcs) == n*(n-1)//2
        assert all(sum(row) == n//2 for row in t.adjacency)
        assert t.is_automorphism(tuple((v+1)%n for v in range(n)))
        assert sum(1 for _ in automorphisms(t.adjacency)) == expected_order
        assert distinguishing_report(t)["distinguishing"]
    invalid = [(0,set()), (2,{1}), (5,{1,4}), (5,{1,2,3}), (3,{0}), (3,{-1})]
    for n, s in invalid:
        try:
            CyclicTournament(n,frozenset(s))
        except ValueError:
            continue
        raise AssertionError((n,s))
    result = {"status": "PASS", "independent_oracle_comparisons": comparisons,
              "oracle": "All permutations, tested directly on every directed adjacency entry",
              "coverage": "All tournaments of orders 1 through 5, each uncolored and 2-colored; 30 seeded random tournaments at orders 6 and 7, each uncolored and 3-colored",
              "known_example_group_orders": [x[2] for x in examples],
              "invalid_connector_cases_rejected": len(invalid),
              "seed": 20261028}
    path = Path(__file__).resolve().parent / "implementation_check_results.json"
    path.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
