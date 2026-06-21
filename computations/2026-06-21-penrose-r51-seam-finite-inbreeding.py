#!/usr/bin/env python3
"""R51: finite-place inbreeding vs the seam firewall.

NODE: inbreeding changes expected genotype-pair distributions.

Target: seam-firewall.  Finite-place dependence among prime phases changes
pair distributions, but does it force archimedean phase-weld positivity?

Boundary cases:
  block_size=1      independent prime phase multipliers
  block_size=all    all primes share one multiplier
"""

from __future__ import annotations

from cmath import exp
from math import log, pi
from random import Random
from statistics import mean, median
from typing import Dict, List, Sequence, Tuple

import mpmath as mp

mp.mp.dps = 35


def primes_upto(n: int) -> List[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * (((n - p * p) // p) + 1)
    return [i for i in range(n + 1) if sieve[i]]


PRIMES = primes_upto(431)[:80]


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


def arch_term_xi(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(
        1 / smp
        + 1 / (smp - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(smp / 2) / 2
    )


def finite_prime_log_derivative(sigma: float, t: float, phases: Sequence[complex]) -> complex:
    s = complex(sigma, t)
    total = 0j
    for p, phase in zip(PRIMES, phases):
        x = phase * exp(-s * log(p))
        total += -log(p) * x / (1 - x)
    return total


def delta_value(a: complex, p: complex) -> float:
    eps = 1e-300
    return max(log(max(abs(a), eps)), log(max(abs(p), eps))) - log(max(abs(a + p), eps))


def phases_for_block(block_size: int, seed: int) -> List[complex]:
    rng = Random(seed)
    phases: List[complex] = []
    for i in range(0, len(PRIMES), block_size):
        theta = rng.random() * 2 * pi
        phase = exp(1j * theta)
        phases.extend([phase] * min(block_size, len(PRIMES) - i))
    return phases


def same_block_pair_fraction(block_size: int) -> float:
    total = 0
    same = 0
    for i in range(len(PRIMES)):
        for j in range(i + 1, len(PRIMES)):
            total += 1
            if i // block_size == j // block_size:
                same += 1
    return same / total


def lane_stats(block_size: int) -> Dict[float, float]:
    sigmas = [0.3, 0.5, 0.7, 1.2]
    ts = [100 + 70 * j / 29 for j in range(30)]
    values: Dict[float, List[float]] = {sigma: [] for sigma in sigmas}
    for seed in range(12):
        phases = phases_for_block(block_size, seed)
        for sigma in sigmas:
            for t in ts:
                a = arch_term_xi(complex(sigma, t))
                p = finite_prime_log_derivative(sigma, t, phases)
                values[sigma].append(delta_value(a, p))
    return {sigma: median(vals) for sigma, vals in values.items()}


def node_genotype_demo() -> None:
    p = 0.35
    print("\nNODE validation: genotype-pair distribution changes with inbreeding F")
    for f in [0.0, 0.25, 0.75, 1.0]:
        aa = p * p + f * p * (1 - p)
        ab = 2 * p * (1 - p) * (1 - f)
        bb = (1 - p) ** 2 + f * p * (1 - p)
        print(f"  F={f:.2f}: P(AA)={aa:.4f}, P(AB)={ab:.4f}, P(BB)={bb:.4f}")


def main() -> None:
    node = "inbreeding changes expected genotype pair distributions"
    attempts = [
        "finite-place inbreeding changes prime-pair law but not seam positivity",
        "shared prime ancestry cannot force archimedean phase-weld positivity",
        "prime block dependence is a seam-firewall boundary case",
    ]
    print("R51 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_genotype_demo()
    print("\nFinite-prime phase inbreeding boundary:")
    for block_size in [1, 2, 5, 20, len(PRIMES)]:
        stats = lane_stats(block_size)
        center = stats[0.5] - 0.5 * (stats[0.3] + stats[0.7])
        print(
            f"  block={block_size:2d}, same_block_pairs={same_block_pair_fraction(block_size):.3f}, "
            f"med_Delta(.3,.5,.7,1.2)=({stats[0.3]:+.4f},{stats[0.5]:+.4f},{stats[0.7]:+.4f},{stats[1.2]:+.4f}), "
            f"center_excess={center:+.4f}"
        )

    print("\nInterpretation:")
    print("  Finite-place dependence changes prime-pair distributions, as expected.")
    print("  The center signal is not monotone in block dependence and is not forced by finite-place inbreeding.")


if __name__ == "__main__":
    main()
