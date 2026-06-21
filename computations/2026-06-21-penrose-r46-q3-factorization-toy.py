#!/usr/bin/env python3
"""R46: coupled-wait factorization failure as a Q3 toy model.

NODE: coupled waiting times can break factorization of multi-time probabilities.
Target: C-2026-06-18-018 (Q3 / higher-Chowla): Q1 is fake-blind, first
discriminator is Q3.

This is only a toy separation test.  It does not supply the missing Q3 ->
kappa_- faithful-index formula.
"""

from __future__ import annotations

from itertools import product
from math import sqrt
from random import Random
from statistics import mean
from typing import Iterable, List, Sequence, Tuple


Triple = Tuple[int, int, int]


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def independent_triples(n: int, seed: int) -> List[Triple]:
    rng = Random(seed)
    return [
        tuple(1 if rng.random() < 0.5 else -1 for _ in range(3))  # type: ignore
        for _ in range(n)
    ]


def parity_coupled_triples(n: int, seed: int) -> List[Triple]:
    rng = Random(seed)
    out: List[Triple] = []
    for _ in range(n):
        x = 1 if rng.random() < 0.5 else -1
        y = 1 if rng.random() < 0.5 else -1
        z = x * y
        out.append((x, y, z))
    return out


def moments(samples: Sequence[Triple]) -> Tuple[List[float], List[List[float]], float]:
    singles = [mean([s[i] for s in samples]) for i in range(3)]
    pairs: List[List[float]] = []
    for i in range(3):
        row = []
        for j in range(3):
            row.append(mean([s[i] * s[j] for s in samples]))
        pairs.append(row)
    triple = mean([s[0] * s[1] * s[2] for s in samples])
    return singles, pairs, triple


def frob_pair_error(pairs: Sequence[Sequence[float]]) -> float:
    total = 0.0
    for i in range(3):
        for j in range(3):
            target = 1.0 if i == j else 0.0
            total += (pairs[i][j] - target) ** 2
    return sqrt(total)


def exact_distributions() -> None:
    independent = list(product([-1, 1], repeat=3))
    parity = [(x, y, x * y) for x, y in product([-1, 1], repeat=2)]

    def exact_moment(dist: Sequence[Triple], func) -> float:
        return sum(func(t) for t in dist) / len(dist)

    print("\nExact support check:")
    print(f"  independent support size={len(independent)}, parity support size={len(parity)}")
    print("  parity singles:", [exact_moment(parity, lambda t, i=i: t[i]) for i in range(3)])
    print(
        "  parity pair moments:",
        [exact_moment(parity, lambda t, i=i, j=j: t[i] * t[j]) for i in range(3) for j in range(i + 1, 3)],
    )
    print(f"  parity triple moment={exact_moment(parity, lambda t: t[0]*t[1]*t[2]):.1f}")


def main() -> None:
    node = "coupled waiting times can break usual factorization of multi-time probabilities"
    attempts = [
        "Q1 pairwise factorization blind Q3 triple parity detects coupling",
        "higher Chowla is the first joint renewal-factorization test",
        "waiting-time coupling maps to a third cumulant fake separator",
    ]
    print("R46 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    exact_distributions()
    n = 200_000
    for name, samples in [
        ("independent", independent_triples(n, 1)),
        ("parity_coupled", parity_coupled_triples(n, 2)),
    ]:
        singles, pairs, triple = moments(samples)
        print(f"\n{name}:")
        print(f"  singles={['%+.4f' % x for x in singles]}")
        print(f"  Q1_pair_frobenius_error_to_identity={frob_pair_error(pairs):.6f}")
        print(f"  Q3_triple_moment={triple:+.6f}")

    print("\nSubclaim split:")
    print("  A: Q3 can separate a fake family invisible to Q1 pairwise PSD: supported by the parity toy.")
    print("  B: this Q3 index equals kappa_- for xi/source data: not supplied here; remains the target obstruction.")


if __name__ == "__main__":
    main()
