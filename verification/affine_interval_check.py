"""Exhaustively check affine half-interval stabilizers for odd n <= 101.

Standard library only. These finite checks are not premises of the proof.
"""
from __future__ import annotations

import json
from math import gcd
from pathlib import Path


def check(maximum: int = 101) -> dict:
    records = []
    for n in range(3, maximum + 1, 2):
        q = (n - 1) // 2
        half = frozenset(range(q + 1))
        correlations = [
            len(half & frozenset((x + d) % n for x in half))
            for d in range(n)
        ]
        assert correlations[0] == q + 1
        assert correlations[1:] == [
            q + 1 - min(d, n - d) for d in range(1, n)
        ]
        assert {
            d for d in range(1, n) if correlations[d] == q
        } == {1, n - 1}
        stabilizer = []
        candidates = 0
        for alpha in range(n):
            if gcd(alpha, n) != 1:
                continue
            for beta in range(n):
                candidates += 1
                if frozenset((alpha * x + beta) % n for x in half) == half:
                    stabilizer.append([alpha, beta])
                    assert all(
                        correlations[(alpha * d) % n] == correlations[d]
                        for d in range(n)
                    )
        assert stabilizer == [[1, 0], [n - 1, q]], (n, stabilizer)
        records.append({
            "n": n,
            "q": q,
            "affine_permutations_checked": candidates,
            "stabilizer": stabilizer,
        })
    return {
        "orders": len(records),
        "largest_order": maximum,
        "total_affine_permutations_checked": sum(
            row["affine_permutations_checked"] for row in records
        ),
        "all_checks_passed": True,
        "records": records,
    }


if __name__ == "__main__":
    result = check()
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print({key: value for key, value in result.items() if key != "records"})
