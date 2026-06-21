#!/usr/bin/env python3
"""R69: scalar Gaussian marginals versus oriented 2-form carrier.

NODE: fBm displacement density can remain Gaussian while variance scales as
t^(2H).

Target: C1 carrier is an oriented 2-form, not a scalar.  Extreme-case test:
time reversal preserves scalar samples but flips oriented phase-space area.
"""

from __future__ import annotations

from math import atan2, log
from statistics import mean
from typing import List, Tuple

import mpmath as mp
import numpy as np

mp.mp.dps = 35


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_validation() -> None:
    print("\nNODE validation: Gaussian marginal, anomalous variance scale")
    rng = np.random.default_rng(69)
    times = np.array([1, 2, 4, 8, 16], dtype=float)
    for H in [0.3, 0.5, 0.8]:
        samples = [rng.normal(0.0, t**H, 20_000) for t in times]
        variances = [float(np.var(x)) for x in samples]
        slope = np.polyfit(np.log(times), np.log(variances), 1)[0]
        print(f"  H={H:.1f}: fitted variance exponent={slope:.3f}, expected={2*H:.3f}")


def zeta_log_derivative(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(mp.diff(mp.zeta, smp) / mp.zeta(smp))


def area(points: List[Tuple[float, float]]) -> float:
    total = 0.0
    for (x0, y0), (x1, y1) in zip(points, points[1:]):
        total += x0 * y1 - x1 * y0
    return 0.5 * total


def unwrap(phases: List[float]) -> List[float]:
    out = [phases[0]]
    for p in phases[1:]:
        q = p
        while q - out[-1] > np.pi:
            q -= 2 * np.pi
        while q - out[-1] < -np.pi:
            q += 2 * np.pi
        out.append(q)
    return out


def target_test() -> None:
    sigma = 0.3
    lo, hi = 100.0, 170.0
    pts: List[Tuple[float, float]] = []
    phases = []
    amps = []
    for j in range(80):
        t = lo + (hi - lo) * j / 79
        p = zeta_log_derivative(complex(sigma, t))
        amps.append(log(1 + abs(p)))
        phases.append(atan2(p.imag, p.real))
    ph_unwrapped = unwrap(phases)
    pts = list(zip(amps, ph_unwrapped))
    rev_pts = list(reversed(pts))
    print("\nTarget test: scalar samples identical, oriented area flips")
    print(f"  scalar amplitude mean original={mean(amps):.6f}, reversed={mean(list(reversed(amps))):.6f}")
    print(f"  scalar amplitude sorted maxdiff={max(abs(a-b) for a,b in zip(sorted(amps), sorted(reversed(amps)))):.3e}")
    print(f"  oriented area original={area(pts):.6f}")
    print(f"  oriented area reversed={area(rev_pts):.6f}")


def main() -> None:
    node = "the probability density remains Gaussian while its variance scales as t^(2H)"
    attempts = [
        "scalar marginal shape can miss the oriented carrier",
        "C1 needs area orientation not Gaussian scalar samples",
        "same scalar distribution can have opposite transport two-form",
    ]
    print("R69 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    target_test()

    print("\nInterpretation:")
    print("  Scalar samples can be identical while the oriented area changes sign.")
    print("  This confirms C1's warning, but it is the generic reason C1 exists.")


if __name__ == "__main__":
    main()
