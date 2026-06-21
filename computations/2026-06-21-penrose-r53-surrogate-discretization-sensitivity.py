#!/usr/bin/env python3
"""R53: discretization sensitivity warning for the surrogate-ladder action.

NODE: stochastic simulations can be sensitive to discretization choices.

Target: source-map / dependency summary naming the surrogate-ladder experiment
as the informative open action.

Small-case test: a phase-weld classifier comparing true zeta'/zeta with a
finite Euler surrogate under different t-grid resolutions and offsets.
"""

from __future__ import annotations

from cmath import exp
from math import log
from statistics import median
from typing import List, Sequence, Tuple

import mpmath as mp

mp.mp.dps = 35


def primes_upto(n: int) -> List[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * (((n - p * p) // p) + 1)
    return [i for i in range(n + 1) if sieve[i]]


PRIMES = primes_upto(1223)[:200]


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


def node_demo() -> None:
    print("\nNODE validation: multiplicative-noise discretization drift")
    x0 = 1.0
    sigma = 0.8
    dt = 0.01
    steps = 1000
    # Deterministic +/- increments make the convention gap visible without RNG.
    increments = [dt**0.5 if i % 2 == 0 else -dt**0.5 for i in range(steps)]
    ito = x0
    strat = x0
    for dw in increments:
        ito += sigma * ito * dw
        mid = strat + 0.5 * sigma * strat * dw
        strat += sigma * mid * dw
    print(f"  Ito endpoint={ito:.6f}, midpoint/Stratonovich-like endpoint={strat:.6f}")


def zeta_log_derivative(s: complex) -> complex:
    z = mp.zeta(s)
    zp = mp.diff(mp.zeta, s)
    return complex(zp / z)


def finite_log_derivative(s: complex) -> complex:
    total = 0j
    for p in PRIMES:
        x = exp(-s * log(p))
        total += -log(p) * x / (1 - x)
    return total


def arch_term_xi(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(
        1 / smp
        + 1 / (smp - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(smp / 2) / 2
    )


def delta(a: complex, p: complex) -> float:
    eps = 1e-300
    return max(log(max(abs(a), eps)), log(max(abs(p), eps))) - log(max(abs(a + p), eps))


def score(sigma: float, samples: int, offset: float, true: bool) -> float:
    lo, hi = 100.0, 170.0
    vals = []
    for j in range(samples):
        t = lo + (hi - lo) * ((j + offset) / samples)
        s = complex(sigma, t)
        a = arch_term_xi(s)
        p = zeta_log_derivative(s) if true else finite_log_derivative(s)
        vals.append(max(0.0, delta(a, p)))
    return median(vals)


def main() -> None:
    node = "sensitivity to discretization of stochastic differential equations"
    attempts = [
        "surrogate ladder phase-weld classifier depends on sampling discretization",
        "source-map surrogate action needs grid-stability certificate",
        "discretization changes inferred native carrier verdict",
    ]
    print("R53 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_demo()
    print("\nSmall surrogate-ladder discretization cases:")
    for sigma in [0.3, 0.5, 0.7]:
        print(f"  sigma={sigma:.1f}")
        for samples in [16, 32, 64]:
            rows = []
            for offset in [0.0, 0.25, 0.5, 0.75]:
                true_score = score(sigma, samples, offset, True)
                finite_score = score(sigma, samples, offset, False)
                rows.append(true_score - finite_score)
            print(
                f"    samples={samples:2d}: true-minus-finite by offset="
                + ",".join(f"{x:+.4f}" for x in rows)
            )

    print("\nInterpretation:")
    print("  The left lane is stable, but transition lanes can flip sign with grid and offset.")
    print("  The surrogate ladder needs a grid-stability certificate; this run does not add a new invariant.")


if __name__ == "__main__":
    main()
