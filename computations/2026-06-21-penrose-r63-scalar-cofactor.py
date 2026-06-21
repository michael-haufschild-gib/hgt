#!/usr/bin/env python3
"""R63: scalar-layer reshaping by cofactors.

NODE: cofactors / modifications can reshape a conformational landscape and
change the apparent mechanism.

Target: Scalar Layer.  Invariant test: positive scalar cofactors can strongly
reshape log(1+|P|), while phase direction is unchanged.  This reinforces that
scalar amplitude is not a native invariant.
"""

from __future__ import annotations

from math import atan2, cos, log, pi, sin
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
    print("\nNODE validation: cofactor reshapes apparent landscape weights")
    energies = np.array([0.0, 0.4, 0.8])
    cofactor_shift = np.array([0.6, -0.3, 0.0])
    for temp in [0.7, 1.0]:
        base = np.exp(-energies / temp)
        shifted = np.exp(-(energies + cofactor_shift) / temp)
        base /= base.sum()
        shifted /= shifted.sum()
        print(f"  T={temp:.1f}: base_pop={base.round(3).tolist()} cofactor_pop={shifted.round(3).tolist()}")


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


def cos_ap(a: complex, p: complex) -> float:
    denom = abs(a) * abs(p)
    return ((a * p.conjugate()).real / denom) if denom else 0.0


def target_test(window: Tuple[float, float] = (100.0, 170.0), sigma: float = 0.3, points: int = 42) -> None:
    beta_before: List[float] = []
    beta_after: List[float] = []
    phase_before: List[float] = []
    phase_after: List[float] = []
    cos_before: List[float] = []
    cos_after: List[float] = []
    lo, hi = window
    for j in range(points):
        t = lo + (hi - lo) * j / (points - 1)
        s = complex(sigma, t)
        p = zeta_log_derivative(s)
        a = arch_term_xi(s)
        cofactor = 1.0 + 0.65 * (0.5 + 0.5 * sin(2 * pi * (t - lo) / 11.0))
        pc = cofactor * p
        beta_before.append(log(1 + abs(p)))
        beta_after.append(log(1 + abs(pc)))
        phase_before.append(atan2(p.imag, p.real))
        phase_after.append(atan2(pc.imag, pc.real))
        cos_before.append(cos_ap(a, p))
        cos_after.append(cos_ap(a, pc))

    beta_shift = [b2 - b1 for b1, b2 in zip(beta_before, beta_after)]
    phase_shift = [abs(ph2 - ph1) for ph1, ph2 in zip(phase_before, phase_after)]
    cos_shift = [abs(c2 - c1) for c1, c2 in zip(cos_before, cos_after)]
    print("\nTarget test: positive cofactor reshapes scalar layer")
    print(f"  sigma={sigma}, window={int(window[0])}-{int(window[1])}, points={points}")
    print(f"  beta shift mean={mean(beta_shift):.6f}, range={min(beta_shift):.6f}..{max(beta_shift):.6f}")
    print(f"  phase shift max={max(phase_shift):.3e}")
    print(f"  cos(A,P) shift max={max(cos_shift):.3e}")


def main() -> None:
    node = "metal ions, cofactors, lipids, or post-translational modifications can reshape the landscape and change apparent mechanisms"
    attempts = [
        "scalar layer changes under smooth cofactors while phase direction does not",
        "cofactor reshaping exposes scalar amplitude as non-invariant",
        "apparent scalar mechanism is not stable under positive landscape modifiers",
    ]
    print("R63 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    target_test()

    print("\nInterpretation:")
    print("  The scalar layer is cofactor-sensitive; phase direction survives positive")
    print("  amplitude modifiers. This is the already-stated scalar-layer warning.")


if __name__ == "__main__":
    main()
