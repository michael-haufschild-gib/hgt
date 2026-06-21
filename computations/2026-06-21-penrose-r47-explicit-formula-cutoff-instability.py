#!/usr/bin/env python3
"""R47: heavy-tail sample instability transferred to explicit-formula cutoffs.

NODE: heavy-tailed waiting times can make sample means unstable and convergence
slow, even with large data.

Target: explicit formula as constraint linking zeros, primes, and the
archimedean term.

Test nearby false statement: a large sharp zero cutoff gives a stable
pointwise explicit-formula estimate.
"""

from __future__ import annotations

from math import isqrt, log, sqrt
from typing import Dict, Iterable, List, Sequence, Tuple

import mpmath as mp

mp.mp.dps = 40


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


def von_mangoldt_upto(n: int) -> List[float]:
    lam = [0.0] * (n + 1)
    is_prime = [True] * (n + 1)
    is_prime[0:2] = [False, False]
    for p in range(2, n + 1):
        if not is_prime[p]:
            continue
        for k in range(p * p, n + 1, p):
            is_prime[k] = False
        pk = p
        lp = log(p)
        while pk <= n:
            lam[pk] = lp
            pk *= p
    return lam


def psi_values(xs: Sequence[int]) -> Dict[int, float]:
    lam = von_mangoldt_upto(max(xs))
    running = 0.0
    out = {}
    targets = set(xs)
    for n in range(1, max(xs) + 1):
        running += lam[n]
        if n in targets:
            out[n] = running
    return out


def zero_gammas(n: int) -> List[float]:
    return [float(mp.im(mp.zetazero(k))) for k in range(1, n + 1)]


def zero_term(x: float, gamma: float) -> float:
    # 2 Re(x^(1/2+i gamma)/(1/2+i gamma))
    u = gamma * log(x)
    denom = 0.25 + gamma * gamma
    return 2 * sqrt(x) * (0.5 * mp.cos(u) + gamma * mp.sin(u)) / denom


def approx_psi(x: int, gammas: Sequence[float], n: int) -> float:
    zero_sum = sum(float(zero_term(x, g)) for g in gammas[:n])
    arch = log(2 * mp.pi) + 0.5 * log(1 - x ** -2)
    return float(x - zero_sum - arch)


def main() -> None:
    node = "heavy-tailed waiting times make sample means unstable and convergence slow even with large data"
    attempts = [
        "sharp explicit-formula cutoffs behave like unstable heavy-tail sample means",
        "smoothed zero sums are the constraint-safe estimator",
        "large zero samples do not imply pointwise explicit-formula convergence",
    ]
    print("R47 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    xs = [100, 1000, 10000]
    cutoffs = [10, 20, 50, 100, 150, 200]
    gammas = zero_gammas(max(cutoffs))
    psi = psi_values(xs)

    print("\nSharp cutoff explicit-formula errors:")
    for x in xs:
        print(f"  x={x}, psi={psi[x]:.6f}")
        prev = None
        for n in cutoffs:
            approx = approx_psi(x, gammas, n)
            err = approx - psi[x]
            jump = err - prev if prev is not None else 0.0
            prev = err
            print(f"    N={n:3d}: approx={approx: .6f}, err={err: .6f}, delta_err={jump: .6f}")

    print("\nLast-block contribution sizes:")
    for x in xs:
        for a, b in [(50, 100), (100, 150), (150, 200)]:
            block = sum(float(zero_term(x, g)) for g in gammas[a:b])
            print(f"  x={x}, block {a+1}-{b}: zero_block={block: .6f}")

    print("\nInterpretation:")
    print("  Sharp zero cutoffs are not stable pointwise estimators of the explicit formula.")
    print("  This supports only the standard distributional/smoothed-test-function warning.")


if __name__ == "__main__":
    main()
