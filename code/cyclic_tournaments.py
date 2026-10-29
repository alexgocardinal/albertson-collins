#!/usr/bin/env python3
"""Construct and exactly check cyclic tournaments, using Python's stdlib only.

The automorphism search compares adjacency entries. It does not use the proposed
Albertson--Collins theorem or assume that automorphisms are affine/translations.
A permutation is represented by a tuple p with p[v] the image of vertex v.
"""
from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from itertools import permutations
import json
from math import cos, pi, sin
from pathlib import Path
from typing import Iterator, Sequence


@dataclass(frozen=True)
class CyclicTournament:
    n: int
    connectors: frozenset[int]

    def __post_init__(self) -> None:
        if not isinstance(self.n, int) or isinstance(self.n, bool) or self.n < 1 or self.n % 2 != 1:
            raise ValueError("n must be a positive odd integer")
        raw = tuple(self.connectors)
        if any(not isinstance(d, int) or isinstance(d, bool) or not 0 < d < self.n for d in raw):
            raise ValueError("connectors must be integers in {1,...,n-1}")
        s = frozenset(raw)
        if any(((d in s) + ((self.n - d) in s)) != 1 for d in range(1, self.n)):
            raise ValueError("choose exactly one residue from every pair {d,-d}")
        object.__setattr__(self, "connectors", s)

    @classmethod
    def from_bits(cls, n: int, bits: int) -> "CyclicTournament":
        if not isinstance(n, int) or isinstance(n, bool) or n < 1 or n % 2 != 1:
            raise ValueError("n must be a positive odd integer")
        q = n // 2
        if not isinstance(bits, int) or isinstance(bits, bool) or not 0 <= bits < 2**q:
            raise ValueError("bits must be an integer between 0 and 2**(n//2)-1")
        return cls(n, frozenset(d if (bits >> (d-1)) & 1 else n-d for d in range(1, q+1)))

    def has_arc(self, u: int, v: int) -> bool:
        if not 0 <= u < self.n or not 0 <= v < self.n:
            raise IndexError("vertex outside {0,...,n-1}")
        return (v-u) % self.n in self.connectors

    @property
    def adjacency(self) -> tuple[tuple[int, ...], ...]:
        return tuple(tuple(int(self.has_arc(u, v)) for v in range(self.n)) for u in range(self.n))

    @property
    def arcs(self) -> tuple[tuple[int, int], ...]:
        return tuple((u, v) for u in range(self.n) for v in range(self.n) if self.has_arc(u, v))

    @property
    def canonical_coloring(self) -> tuple[int, ...]:
        return tuple(1 if v <= self.n//2 else 2 for v in range(self.n))

    def is_automorphism(self, p: Sequence[int], colors: Sequence[int] | None = None) -> bool:
        if len(p) != self.n or set(p) != set(range(self.n)):
            return False
        c = _normalize_colors(self.n, colors)
        return (all(c[v] == c[p[v]] for v in range(self.n)) and
                all(self.has_arc(u, v) == self.has_arc(p[u], p[v])
                    for u in range(self.n) for v in range(self.n)))


def _normalize_colors(n: int, colors: Sequence[int] | None) -> tuple[int, ...]:
    if colors is None:
        return (0,) * n
    c = tuple(colors)
    if len(c) != n:
        raise ValueError("one color is required for each vertex")
    if any(not isinstance(x, int) for x in c):
        raise ValueError("colors must be integers")
    return c


def _validate_adjacency(adjacency: Sequence[Sequence[int]]) -> tuple[tuple[int, ...], ...]:
    a = tuple(tuple(row) for row in adjacency)
    n = len(a)
    if n == 0 or any(len(row) != n for row in a):
        raise ValueError("adjacency must be a nonempty square matrix")
    if any(x not in (0, 1) for row in a for x in row):
        raise ValueError("adjacency entries must be 0 or 1")
    if any(a[v][v] for v in range(n)):
        raise ValueError("tournaments have no loops")
    if any(a[u][v] + a[v][u] != 1 for u in range(n) for v in range(u+1, n)):
        raise ValueError("each distinct pair must have exactly one arc")
    return a


def automorphisms(adjacency: Sequence[Sequence[int]], colors: Sequence[int] | None = None,
                  limit: int | None = None) -> Iterator[tuple[int, ...]]:
    """Enumerate every color-preserving automorphism, optionally stopping at limit.

    This is a complete finite constraint search, not a restriction to an assumed
    automorphism family. Color refinement only removes impossible candidates;
    each partial bijection is checked on all previously assigned pairs.
    """
    a = _validate_adjacency(adjacency)
    n = len(a)
    c = _normalize_colors(n, colors)
    if limit is not None and (not isinstance(limit, int) or limit < 1):
        raise ValueError("limit must be positive, or None")
    labels = {x: i for i, x in enumerate(sorted(set(c)))}
    refined = tuple(labels[x] for x in c)
    while True:
        k = max(refined) + 1
        signatures = []
        for u in range(n):
            out = [0] * k
            inc = [0] * k
            for v in range(n):
                out[refined[v]] += a[u][v]
                inc[refined[v]] += a[v][u]
            signatures.append((refined[u], tuple(out), tuple(inc)))
        ids = {s: i for i, s in enumerate(sorted(set(signatures)))}
        next_colors = tuple(ids[s] for s in signatures)
        if len(ids) == len(set(refined)):
            refined = next_colors
            break
        refined = next_colors
    candidates = [tuple(v for v in range(n) if refined[u] == refined[v]) for u in range(n)]
    mapping = [-1] * n
    assigned: list[int] = []
    used = [False] * n
    yielded = 0

    def domains(u: int) -> list[int]:
        return [v for v in candidates[u] if not used[v]
                and all(a[u][x] == a[v][mapping[x]] and
                        a[x][u] == a[mapping[x]][v] for x in assigned)]

    def search() -> Iterator[tuple[int, ...]]:
        nonlocal yielded
        if limit is not None and yielded >= limit:
            return
        if len(assigned) == n:
            yielded += 1
            yield tuple(mapping)
            return
        best_u = -1
        best_domain: list[int] | None = None
        for u in range(n):
            if mapping[u] < 0:
                ds = domains(u)
                if not ds:
                    return
                if best_domain is None or len(ds) < len(best_domain):
                    best_u, best_domain = u, ds
        assert best_domain is not None
        for v in best_domain:
            mapping[best_u] = v
            used[v] = True
            assigned.append(best_u)
            yield from search()
            assigned.pop()
            used[v] = False
            mapping[best_u] = -1
            if limit is not None and yielded >= limit:
                return

    yield from search()


def distinguishing_report(t: CyclicTournament) -> dict:
    """Exact yes/no result. Stop at the second map if a counterexample is found."""
    found = list(automorphisms(t.adjacency, t.canonical_coloring, limit=2))
    ident = tuple(range(t.n))
    witness = next((p for p in found if p != ident), None)
    return {"n": t.n, "connectors": sorted(t.connectors),
            "canonical_coloring": list(t.canonical_coloring),
            "distinguishing": len(found) == 1 and found[0] == ident,
            "color_preserving_automorphisms_found_up_to_2": len(found),
            "nonidentity_witness": list(witness) if witness is not None else None}


def exhaustive_check(max_n: int = 15) -> dict:
    if max_n < 1 or max_n % 2 != 1:
        raise ValueError("max_n must be positive and odd")
    records = []
    total = 0
    for n in range(1, max_n+1, 2):
        count = 2**(n//2)
        for bits in range(count):
            t = CyclicTournament.from_bits(n, bits)
            result = distinguishing_report(t)
            if not result["distinguishing"]:
                return {"status": "FAIL", "counterexample": result, "checked_before_failure": total}
            total += 1
        records.append({"n": n, "connector_sets": count,
                        "all_canonical_colorings_distinguishing": True})
    return {"status": "PASS", "method": "Exact directed-adjacency automorphism backtracking",
            "orders": records, "total_tournaments": total,
            "scope": "Finite checks of all labelled connector sets at these orders; not an all-order proof."}


def brute_force_automorphisms(adjacency: Sequence[Sequence[int]],
                              colors: Sequence[int] | None = None) -> list[tuple[int, ...]]:
    """Slow independent reference implementation, intended only for small n."""
    a = _validate_adjacency(adjacency)
    n = len(a)
    c = _normalize_colors(n, colors)
    return [p for p in permutations(range(n))
            if all(c[u] == c[p[u]] for u in range(n))
            and all(a[u][v] == a[p[u]][p[v]] for u in range(n) for v in range(u+1, n))]


def export(t: CyclicTournament, directory: str | Path, name: str, title: str | None = None) -> dict:
    """Write JSON, directed arc CSV, adjacency CSV, DOT, and a labelled SVG."""
    out = Path(directory)
    out.mkdir(parents=True, exist_ok=True)
    data = {"schema": "cyclic-tournament-v1", "name": name, "title": title or name,
            "n": t.n, "vertices": list(range(t.n)), "connectors": sorted(t.connectors),
            "arc_rule": "u -> v iff (v-u) mod n is in connectors",
            "canonical_coloring": list(t.canonical_coloring),
            "arcs": [list(e) for e in t.arcs], "adjacency": [list(row) for row in t.adjacency],
            "verification": distinguishing_report(t)}
    if t.n <= 11:
        data["uncolored_automorphism_group_order"] = sum(1 for _ in automorphisms(t.adjacency))
    (out/f"{name}.json").write_text(json.dumps(data, indent=2) + "\n")
    with (out/f"{name}_arcs.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["source", "target"])
        w.writerows(t.arcs)
    with (out/f"{name}_adjacency.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["source/target", *range(t.n)])
        w.writerows((u, *row) for u, row in enumerate(t.adjacency))
    dot = ["digraph tournament {", "  graph [layout=circo];", "  node [style=filled, shape=circle];"]
    for v, c in enumerate(t.canonical_coloring):
        dot.append(f'  {v} [fillcolor="{"#f6b95d" if c == 1 else "#8fc4ea"}", label="{v}"];')
    dot.extend(f"  {u} -> {v};" for u, v in t.arcs)
    dot.append("}")
    (out/f"{name}.dot").write_text("\n".join(dot) + "\n")
    _write_svg(t, out/f"{name}.svg", title or name)
    return data


def _write_svg(t: CyclicTournament, path: Path, title: str) -> None:
    """Precise vector diagram: each arrow is computed from the connector rule."""
    from html import escape
    width, height = 620, 690
    cx, cy, radius, vertex_radius = 310, 335, 235, 20
    points = [(cx+radius*cos(-pi/2 + 2*pi*v/t.n), cy+radius*sin(-pi/2 + 2*pi*v/t.n))
              for v in range(t.n)]
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
             '<rect width="100%" height="100%" fill="#ffffff"/>',
             '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#4b5563"/></marker></defs>',
             f'<text x="310" y="34" text-anchor="middle" font-family="sans-serif" font-size="23" fill="#142e47">{escape(title)}</text>',
             f'<text x="310" y="60" text-anchor="middle" font-family="sans-serif" font-size="15" fill="#4b5563">n = {t.n}; S = {{{", ".join(map(str, sorted(t.connectors)))}}}</text>']
    for u, v in t.arcs:
        x1, y1 = points[u]
        x2, y2 = points[v]
        length = ((x2-x1)**2+(y2-y1)**2)**0.5
        dx, dy = (x2-x1)/length, (y2-y1)/length
        x1, y1 = x1+dx*(vertex_radius+1), y1+dy*(vertex_radius+1)
        x2, y2 = x2-dx*(vertex_radius+4), y2-dy*(vertex_radius+4)
        parts.append(f'<line x1="{x1:.3f}" y1="{y1:.3f}" x2="{x2:.3f}" y2="{y2:.3f}" stroke="#4b5563" stroke-width="1.15" stroke-opacity="0.67" marker-end="url(#arrow)"/>')
    for v, (x, y) in enumerate(points):
        fill = "#f6b95d" if t.canonical_coloring[v] == 1 else "#8fc4ea"
        parts.append(f'<circle cx="{x:.3f}" cy="{y:.3f}" r="{vertex_radius}" fill="{fill}" stroke="#142e47" stroke-width="1.5"/>')
        parts.append(f'<text x="{x:.3f}" y="{y+6:.3f}" text-anchor="middle" font-family="sans-serif" font-size="18" fill="#142e47">{v}</text>')
    parts.extend(['<circle cx="152" cy="635" r="9" fill="#f6b95d" stroke="#142e47"/>',
                  '<text x="170" y="641" font-family="sans-serif" font-size="15">Color 1: 0 through floor(n/2)</text>',
                  '<circle cx="152" cy="663" r="9" fill="#8fc4ea" stroke="#142e47"/>',
                  '<text x="170" y="669" font-family="sans-serif" font-size="15">Color 2: remaining vertices</text>', '</svg>'])
    path.write_text("\n".join(parts) + "\n")


def examples(directory: str | Path) -> dict:
    specifications = [
        ("c3", 3, {1}, "Directed triangle"),
        ("regular5", 5, {1, 2}, "Consecutive-connector tournament"),
        ("paley7", 7, {1, 2, 4}, "Paley tournament on seven vertices"),
        ("wreath9", 9, {1, 3, 4, 7}, "Three directed triangles in a cycle"),
    ]
    results = []
    for name, n, s, title in specifications:
        data = export(CyclicTournament(n, frozenset(s)), directory, name, title)
        results.append({"name": name, "n": n, "connectors": sorted(s),
                        "uncolored_automorphism_group_order": data["uncolored_automorphism_group_order"],
                        "colored_automorphism_group_order": 1 if data["verification"]["distinguishing"] else ">=2"})
    summary = {"examples": results,
               "wreath9_blocks": [[0,3,6],[1,4,7],[2,5,8]],
               "note": "All files preserve arc directions; graph6 would discard the tournament orientation."}
    (Path(directory)/"examples_summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    e = sub.add_parser("examples", help="Export four representative tournaments")
    e.add_argument("--output", default=str(Path(__file__).resolve().parents[1]/"graphs"))
    x = sub.add_parser("exhaustive", help="Check every connector set through a finite odd order")
    x.add_argument("--max-n", type=int, default=15)
    x.add_argument("--output", type=Path)
    one = sub.add_parser("one", help="Export and check an explicitly specified tournament")
    one.add_argument("n", type=int)
    one.add_argument("--connectors", required=True, help="comma-separated integers, e.g. 1,2,4")
    one.add_argument("--name", default="custom")
    one.add_argument("--output", default="graphs")
    args = parser.parse_args()
    if args.command == "examples":
        result = examples(args.output)
    elif args.command == "exhaustive":
        result = exhaustive_check(args.max_n)
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2)+"\n")
    else:
        s = frozenset(int(x) for x in args.connectors.split(",") if x.strip())
        result = export(CyclicTournament(args.n, s), args.output, args.name)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
