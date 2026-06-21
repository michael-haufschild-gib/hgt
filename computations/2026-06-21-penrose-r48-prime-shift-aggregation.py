#!/usr/bin/env python3
"""R48: heterogeneous aggregation creates apparent power laws in prime shifts.

NODE: aggregating heterogeneous individuals can create apparent power laws even
when no individual follows one.

Target: G_a prime shifts M_p in the affine ax+b geometry.

Each prime lane has exponential dependence exp(-delta log p).  The aggregate
sum log(p) p^{-(1+delta)} behaves like a pole 1/delta by PNT, showing how a
continuum-looking singularity can be manufactured by heterogeneous prime-shift
rates.
"""

from __future__ import annotations

from math import log
from typing import List


def primes_upto(n: int) -> List[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : n + 1 : p] = b"\x00" * (((n - start) // p) + 1)
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


def main() -> None:
    node = "aggregating heterogeneous individuals can create apparent power laws even when no individual follows one"
    attempts = [
        "aggregate prime shifts create pole although each lane is exponential",
        "G_a heterogeneity manufactures apparent continuum scaling",
        "prime-shift mixture is power-law-looking but individual primes are not",
    ]
    print("R48 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    x = 2_000_000
    primes = primes_upto(x)
    deltas = [0.02, 0.03, 0.05, 0.08, 0.12, 0.20]
    print(f"\nPrime-shift aggregate up to X={x}, pi(X)={len(primes)}")
    print("  A(delta)=sum_{p<=X} log(p) p^{-(1+delta)}; pole test delta*A(delta)")
    for delta in deltas:
        terms = [log(p) * p ** (-(1 + delta)) for p in primes]
        agg = sum(terms)
        largest_share = max(terms) / agg
        print(
            f"  delta={delta:.3f}: A={agg:.6f}, delta*A={delta*agg:.6f}, "
            f"largest_lane_share={largest_share:.6f}"
        )

    print("\nASCII visual: delta*A(delta), ideal pole would be near 1")
    for delta in deltas:
        agg = sum(log(p) * p ** (-(1 + delta)) for p in primes)
        value = delta * agg
        bar = "#" * int(40 * min(value, 1.2) / 1.2)
        print(f"  {delta:0.3f} | {bar} {value:.3f}")

    print("\nInterpretation:")
    print("  No single prime lane has a power law in delta; the pole is an aggregate over heterogeneous log p rates.")
    print("  This is substrate/PNT behavior of G_a, not RH-bearing content.")


if __name__ == "__main__":
    main()
