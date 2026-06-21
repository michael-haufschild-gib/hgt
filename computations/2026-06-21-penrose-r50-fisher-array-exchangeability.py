#!/usr/bin/env python3
"""R50: Aldous-Hoover warning transferred to Fisher-style prime norms.

NODE: arrays and networks need Aldous-Hoover-style analogues, not ordinary
sequence de Finetti alone.

Target: Fisher signature wall.  Compare a sequence prime norm with two
array-level quantities:

  S_X(sigma) = sum_p p^{-2 sigma}
  E_X(sigma) = sum_{p<q} (p q)^{-2 sigma}
  R_X(sigma) = sum_p p^{-2 sigma} (sum_{q != p} q^{-sigma})^2

E is the independent-edge square norm and has the same 1/2 wall as S.  R is a
shared-prime row-interaction mass, a toy proxy for a node-latent array
dependence that ordinary sequence exchangeability would miss.
"""

from __future__ import annotations

from math import log
from typing import List


def primes_upto(n: int) -> List[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * (((n - p * p) // p) + 1)
    return [i for i in range(n + 1) if sieve[i]]


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


def quantities(primes: List[int], sigma: float) -> tuple[float, float, float]:
    a = [p ** (-sigma) for p in primes]
    s2 = sum(x * x for x in a)
    s4 = sum(x**4 for x in a)
    edge = 0.5 * (s2 * s2 - s4)
    total_a = sum(a)
    row = sum((x * x) * (total_a - x) ** 2 for x in a)
    return s2, edge, row


def main() -> None:
    node = "arrays and networks need Aldous Hoover analogues not ordinary sequence de Finetti alone"
    attempts = [
        "Fisher sequence wall misses shared prime array row interactions",
        "array exchangeability changes the prime Fisher diagnostic",
        "Aldous-Hoover prime network mass is not a one-index Fisher norm",
    ]
    print("R50 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    xs = [1_000, 10_000, 100_000]
    sigmas = [0.45, 0.55, 0.70, 1.20]
    for x in xs:
        primes = primes_upto(x)
        print(f"\nX={x}, pi(X)={len(primes)}")
        for sigma in sigmas:
            seq, edge, row = quantities(primes, sigma)
            print(
                f"  sigma={sigma:.2f}: S={seq:.6f}, E={edge:.6f}, "
                f"R={row:.6f}, R/E={row/edge if edge else float('inf'):.3f}"
            )

    print("\nGrowth visual for shared-row interaction R_X:")
    for sigma in sigmas:
        vals = [quantities(primes_upto(x), sigma)[2] for x in xs]
        bars = ["#" * min(50, int(8 * log(1 + v))) for v in vals]
        print(f"  sigma={sigma:.2f}: " + " | ".join(f"{x}:{bar} {v:.2f}" for x, bar, v in zip(xs, bars, vals)))

    print("\nInterpretation:")
    print("  The independent-edge norm E adds no new wall beyond the sequence Fisher norm.")
    print("  The shared-row interaction R grows by product-sum algebra and is an array-model warning, not RH content.")


if __name__ == "__main__":
    main()
