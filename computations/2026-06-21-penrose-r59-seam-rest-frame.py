#!/usr/bin/env python3
"""R59: preferred-frame warning for seam localization.

NODE: analog false-vacuum systems often have a preferred rest frame, so exact
relativistic symmetry is only approximate/emergent.

Target: the seam Re(s)=1/2 localized many ways.  Change viewpoint: test the
seam as mirror-frame invariance.  Prime-only coordinates carry a preferred
Euler side; the completed transport should remove that frame bias.
"""

from __future__ import annotations

from math import log, pi, sqrt
from statistics import mean
from typing import Callable, Iterable, List, Tuple

import mpmath as mp

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
    print("\nNODE validation: preferred medium frame in dispersive analog")
    c = 1.0
    alpha = 0.08
    print("  dispersion omega^2 = c^2 k^2 + alpha k^4")
    for k in [0.05, 0.2, 0.5, 1.0, 2.0, 4.0]:
        omega = sqrt(c * c * k * k + alpha * k**4)
        phase_velocity = omega / k
        print(f"  k={k:4.2f}: phase_velocity={phase_velocity:.6f}, deviation={phase_velocity-c:+.6f}")


def zeta_log_derivative(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(mp.diff(mp.zeta, smp) / mp.zeta(smp))


def arch_term_xi(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(
        1 / smp
        + 1 / (smp - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(smp / 2) / 2
    )


def completed_log_derivative(s: complex) -> complex:
    return arch_term_xi(s) + zeta_log_derivative(s)


def lane_imbalance(
    f: Callable[[complex], complex], delta: float, window: Tuple[float, float], points: int = 32
) -> Tuple[float, float]:
    vals: List[float] = []
    lo, hi = window
    for j in range(points):
        t = lo + (hi - lo) * j / (points - 1)
        right = f(complex(0.5 + delta, t))
        left = f(complex(0.5 - delta, t))
        vals.append(abs(log(max(abs(right), 1e-300)) - log(max(abs(left), 1e-300))))
    return mean(vals), max(vals)


def seam_frame_test() -> None:
    windows = [(100.0, 170.0), (500.0, 570.0)]
    deltas = [0.05, 0.10, 0.20]
    print("\nTarget test: mirror-lane magnitude imbalance around Re(s)=1/2")
    print("  window     delta    prime_mean  completed_mean  prime_max  completed_max")
    for window in windows:
        for delta in deltas:
            p_mean, p_max = lane_imbalance(zeta_log_derivative, delta, window)
            h_mean, h_max = lane_imbalance(completed_log_derivative, delta, window)
            print(
                f"  {int(window[0]):4d}-{int(window[1]):4d}  {delta:5.2f}  "
                f"{p_mean:10.6f}  {h_mean:14.6e}  {p_max:9.6f}  {h_max:13.6e}"
            )


def main() -> None:
    node = "the background medium often defines a preferred rest frame, so exact relativistic symmetry is only approximate or emergent"
    attempts = [
        "prime-only seam diagnostics carry a preferred Euler-side frame",
        "completion restores mirror-frame invariance at the critical seam",
        "seam localization must be tested in the completed rest frame",
    ]
    print("R59 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    seam_frame_test()

    print("\nInterpretation:")
    print("  The completed log-derivative removes mirror-lane magnitude imbalance,")
    print("  while prime-only zeta'/zeta keeps a preferred side. This is correct,")
    print("  but it is the existing functional-equation/Berry lane-equalization fact.")


if __name__ == "__main__":
    main()
