#!/usr/bin/env python3
"""R65: local-detailed-balance style cycle affinity for the two-clock layer.

NODE: local detailed-balance constraints on transition rates in stochastic
assembly models.

Target: Two-Clock layer.  Strengthened test: instead of static correlation,
build a directed four-state transition cycle from
    F(t) = finite-prime phase agreement with true zeta'/zeta
    T(t) = true phase-weld tension Delta(A,P_true)
and measure the cycle affinity
    log Π k_forward / Π k_reverse.
"""

from __future__ import annotations

from math import atan2, cos, log, pi
from random import Random
from statistics import median
from typing import Dict, List, Sequence, Tuple

import mpmath as mp

mp.mp.dps = 35


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur[-1:] + cur[1:] if False else cur
    return prev[-1]


def node_validation() -> None:
    print("\nNODE validation: detailed-balance transition-ratio toy")
    for affinity in [0.0, 0.7, 1.5, -0.7]:
        k_forward = 1.0
        k_reverse = k_forward / mp.e**affinity
        print(f"  affinity={float(affinity): .2f}: k_forward/k_reverse={float(k_forward/k_reverse):.4f}")


def primes_upto(n: int) -> List[int]:
    sieve = [True] * (n + 1)
    out = []
    for p in range(2, n + 1):
        if sieve[p]:
            out.append(p)
            for q in range(p * p, n + 1, p):
                sieve[q] = False
    return out


PRIMES = primes_upto(220)


def zeta_log_derivative(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(mp.diff(mp.zeta, smp) / mp.zeta(smp))


def finite_euler_logderivative(s: complex, cutoff: int = 160) -> complex:
    total = 0j
    for p in PRIMES:
        if p > cutoff:
            break
        z = p ** (-s)
        total -= log(p) * z / (1.0 - z)
    return total


def arch_term_xi(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(
        1 / smp
        + 1 / (smp - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(smp / 2) / 2
    )


def phase(z: complex) -> float:
    return atan2(z.imag, z.real)


def phase_agreement(a: complex, b: complex) -> float:
    return cos(phase(a) - phase(b))


def delta(a: complex, p: complex) -> float:
    return max(log(max(abs(a), 1e-300)), log(max(abs(p), 1e-300))) - log(max(abs(a + p), 1e-300))


def cycle_affinity(f_vals: Sequence[float], t_vals: Sequence[float]) -> Tuple[float, Dict[Tuple[int, int], int]]:
    f_med = median(f_vals)
    t_med = median(t_vals)
    states = [(int(f > f_med), int(t > t_med)) for f, t in zip(f_vals, t_vals)]
    counts: Dict[Tuple[int, int], int] = {}
    labels = {(0, 0): 0, (1, 0): 1, (1, 1): 2, (0, 1): 3}
    seq = [labels[s] for s in states]
    for a, b in zip(seq, seq[1:]):
        if a == b:
            continue
        counts[(a, b)] = counts.get((a, b), 0) + 1
    forward = [(0, 1), (1, 2), (2, 3), (3, 0)]
    reverse = [(1, 0), (2, 1), (3, 2), (0, 3)]
    alpha = 0.5
    prod_f = 1.0
    prod_r = 1.0
    for edge in forward:
        prod_f *= counts.get(edge, 0) + alpha
    for edge in reverse:
        prod_r *= counts.get(edge, 0) + alpha
    return log(prod_f / prod_r), counts


def series(window: Tuple[float, float], sigma: float, points: int = 72) -> Tuple[List[float], List[float], List[float]]:
    rng = Random(int(window[0]) + int(1000 * sigma) + 65)
    f_finite: List[float] = []
    f_random: List[float] = []
    tensions: List[float] = []
    lo, hi = window
    for j in range(points):
        t = lo + (hi - lo) * j / (points - 1)
        s = complex(sigma, t)
        p_true = zeta_log_derivative(s)
        p_fin = finite_euler_logderivative(s)
        theta = 2 * pi * rng.random()
        p_rand = abs(p_fin) * complex(mp.cos(theta), mp.sin(theta))
        a = arch_term_xi(s)
        f_finite.append(phase_agreement(p_true, p_fin))
        f_random.append(phase_agreement(p_true, p_rand))
        tensions.append(delta(a, p_true))
    return f_finite, f_random, tensions


def target_test() -> None:
    print("\nTarget test: two-clock directed cycle affinity")
    print("  sigma  window      finite_affinity  random_affinity  finite_edges  random_edges")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            f_fin, f_rand, tension = series(window, sigma)
            aff_fin, cnt_fin = cycle_affinity(f_fin, tension)
            aff_rand, cnt_rand = cycle_affinity(f_rand, tension)
            print(
                f"  {sigma:4.1f}  {int(window[0]):4d}-{int(window[1]):4d}      "
                f"{aff_fin:10.4f}      {aff_rand:10.4f}      {sum(cnt_fin.values()):4d}        {sum(cnt_rand.values()):4d}"
            )


def main() -> None:
    node = "local detailed-balance constraints on transition rates in stochastic assembly models"
    attempts = [
        "two-clock layer should satisfy a directed transition-affinity test",
        "finite-prime phase agreement and true tension form a nonequilibrium clock cycle",
        "local detailed balance becomes cycle current in phase-weld clocks",
    ]
    print("R65 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    target_test()

    print("\nInterpretation:")
    print("  Nonzero cycle affinity would strengthen the two-clock layer beyond")
    print("  static correlation. Controls decide whether this is new or just another")
    print("  phase-carrier transition statistic.")


if __name__ == "__main__":
    main()
