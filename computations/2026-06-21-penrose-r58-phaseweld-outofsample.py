#!/usr/bin/env python3
"""R58: out-of-sample validation for the phase-weld layer.

NODE: LPPL crash models should be validated by out-of-sample bubble-end
forecasts, not only retrospective fits.

Target: Phase-Weld layer of the landscape/weld geometry:
    Delta = max(log|A|, log|P|) - log|A+P|.

The transfer is a validation protocol, not a new formula: calibrate a
phase-weld classifier on one t-window, then test held-out windows without
retuning.
"""

from __future__ import annotations

from math import cos, log, pi, sin, sqrt
from random import Random
from statistics import mean, median
from typing import Dict, Iterable, List, Sequence, Tuple

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


def lppl_basis(t: np.ndarray, tc: float, m: float, omega: float) -> np.ndarray:
    x = np.maximum(tc - t, 1e-6)
    xm = x**m
    lx = np.log(x)
    return np.column_stack([np.ones_like(t), xm, xm * np.cos(omega * lx), xm * np.sin(omega * lx)])


def lppl_node_validation() -> None:
    rng = np.random.default_rng(58)
    tc_true = 105.0
    m = 0.45
    omega = 7.4
    coeff = np.array([4.0, -0.025, 0.010, -0.006])
    t = np.linspace(10.0, 95.0, 140)
    y = lppl_basis(t, tc_true, m, omega) @ coeff + rng.normal(0.0, 0.003, len(t))
    train = t <= 60.0
    test = t > 60.0
    rows = []
    for tc in np.linspace(96.0, 120.0, 49):
        Xtr = lppl_basis(t[train], tc, m, omega)
        beta, *_ = np.linalg.lstsq(Xtr, y[train], rcond=None)
        train_rmse = float(np.sqrt(np.mean((Xtr @ beta - y[train]) ** 2)))
        Xte = lppl_basis(t[test], tc, m, omega)
        test_rmse = float(np.sqrt(np.mean((Xte @ beta - y[test]) ** 2)))
        rows.append((train_rmse, test_rmse, tc))
    train_best = min(rows, key=lambda r: r[0])
    test_best = min(rows, key=lambda r: r[1])
    near_train = [tc for tr, te, tc in rows if tr <= train_best[0] * 1.03]
    print("\nNODE validation: retrospective LPPL fit versus held-out residual")
    print(f"  train-best tc={train_best[2]:.2f}, train_rmse={train_best[0]:.6f}, heldout_rmse={train_best[1]:.6f}")
    print(f"  heldout-best tc={test_best[2]:.2f}, train_rmse={test_best[0]:.6f}, heldout_rmse={test_best[1]:.6f}")
    print(f"  train-near-optimal tc span (within 3%) = [{min(near_train):.2f}, {max(near_train):.2f}]")


def zeta_log_derivative(s: complex) -> complex:
    smp = mp.mpc(s)
    z = mp.zeta(smp)
    zp = mp.diff(mp.zeta, smp)
    return complex(zp / z)


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


def phase_weld_delta(a: complex, p: complex) -> float:
    eps = 1e-300
    la = log(max(abs(a), eps))
    lp = log(max(abs(p), eps))
    lh = log(max(abs(a + p), eps))
    return max(la, lp) - lh


def window_scores(window: Tuple[float, float], sigma: float, points: int = 28) -> Dict[str, float]:
    rng = Random(int(window[0]) + int(100 * sigma) + 58)
    true_vals: List[float] = []
    finite_vals: List[float] = []
    random_vals: List[float] = []
    lo, hi = window
    for j in range(points):
        t = lo + (hi - lo) * j / (points - 1)
        s = complex(sigma, t)
        a = arch_term_xi(s)
        p_true = zeta_log_derivative(s)
        p_finite = finite_euler_logderivative(s)
        theta = 2 * pi * rng.random()
        p_random = abs(p_true) * complex(cos(theta), sin(theta))
        true_vals.append(phase_weld_delta(a, p_true))
        finite_vals.append(phase_weld_delta(a, p_finite))
        random_vals.append(phase_weld_delta(a, p_random))
    return {
        "true": median(true_vals),
        "finite": median(finite_vals),
        "random": median(random_vals),
        "control_max": max(median(finite_vals), median(random_vals)),
    }


def phaseweld_out_of_sample() -> None:
    sigmas = [0.3, 0.5, 0.7, 1.2]
    windows = [(100.0, 170.0), (500.0, 570.0), (1000.0, 1070.0)]
    train_scores = {sigma: window_scores(windows[0], sigma) for sigma in sigmas}
    thresholds = {
        sigma: 0.5 * (train_scores[sigma]["true"] + train_scores[sigma]["control_max"]) for sigma in sigmas
    }
    print("\nTarget test: train on first window, validate phase-weld median Delta out-of-sample")
    print("  sigma  window       true     finite    random   margin  pass_true  pass_ctrls")
    margins: Dict[float, List[float]] = {sigma: [] for sigma in sigmas}
    for sigma in sigmas:
        for window in windows:
            scores = window_scores(window, sigma)
            margin = scores["true"] - scores["control_max"]
            margins[sigma].append(margin)
            threshold = thresholds[sigma]
            pass_true = scores["true"] > threshold
            pass_ctrls = scores["finite"] <= threshold and scores["random"] <= threshold
            print(
                f"  {sigma:4.1f}  {int(window[0]):4d}-{int(window[1]):4d}  "
                f"{scores['true']:8.4f} {scores['finite']:8.4f} {scores['random']:8.4f} "
                f"{margin:8.4f}    {str(pass_true):5s}      {str(pass_ctrls):5s}"
            )

    print("\nHeld-out margin trend by sigma:")
    for sigma in sigmas:
        held = margins[sigma][1:]
        print(
            f"  sigma={sigma:3.1f}: train_margin={margins[sigma][0]: .4f}, "
            f"heldout_min={min(held): .4f}, heldout_mean={mean(held): .4f}"
        )


def main() -> None:
    node = "model validation should use out-of-sample bubble-end forecasts, not only retrospective fits"
    attempts = [
        "out-of-sample validation of phase-weld Delta across height windows",
        "retrospective phase-weld fits are rejected by held-out windows",
        "nested-window stability is the phase-weld forecast surrogate",
    ]
    print("R58 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    lppl_node_validation()
    phaseweld_out_of_sample()

    print("\nInterpretation:")
    print("  This is a validation protocol for the phase-weld layer. A one-window")
    print("  threshold should not be trusted unless it survives held-out height")
    print("  windows and controls. Whether it is new depends on whether the held-out")
    print("  margins add information beyond the existing phase-carrier corpus.")


if __name__ == "__main__":
    main()
