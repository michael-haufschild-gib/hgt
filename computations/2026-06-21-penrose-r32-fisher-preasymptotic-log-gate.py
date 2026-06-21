#!/usr/bin/env python3
"""
R32 STEP 8/9 transfer to the RNG target:
  Fisher signature wall in docs/consolidated/01-landscape-and-geometry.md.

NODE constraint:
  pre-asymptotic logarithmic corrections can look clean on finite windows.

Target-specific transfer:
  replace time t by distance delta = 2*sigma - 1 from the Fisher wall and
  replace the infinite Fisher metric g=(log zeta)''(2*sigma) by its finite
  Bohr/Gibbs cutoff

      g_X(delta) = Var_{1 <= n <= X, p_n proportional n^(-1-delta)}(log n).

Method #20, "name the missing lemma":
  finite Fisher cutoffs only resolve the pole when delta*log(X) is large.
  Otherwise the pole is hidden by a pre-asymptotic ceiling and power+log fits
  manufacture spurious log exponents.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        row = [i]
        for j, cb in enumerate(b, start=1):
            row.append(
                min(
                    prev[j] + 1,
                    row[-1] + 1,
                    prev[j - 1] + (0 if ca == cb else 1),
                )
            )
        prev = row
    return prev[-1]


def finite_fisher(delta: float, X: int) -> float:
    n = np.arange(1, X + 1, dtype=float)
    logs = np.log(n)
    weights = np.exp(-(1.0 + delta) * logs)
    weights /= weights.sum()
    mean = float(np.sum(weights * logs))
    second = float(np.sum(weights * logs * logs))
    return max(0.0, second - mean * mean)


def continuum_ratio(u: float) -> float:
    # Continuous model for sum_{n<=X} n^{-1-delta}: y=delta*log n
    # has density proportional exp(-y) on [0,u]. The normalized metric
    # g_X(delta)*delta^2 tends to Var(y).
    if u <= 1e-8:
        return u * u / 12.0
    z = 1.0 - math.exp(-u)
    m1 = (1.0 - math.exp(-u) * (u + 1.0)) / z
    m2 = (2.0 - math.exp(-u) * (u * u + 2.0 * u + 2.0)) / z
    return max(0.0, m2 - m1 * m1)


@dataclass
class FitRow:
    X: int
    lo: float
    hi: float
    alpha: float
    beta: float
    rmse: float


def fit_power_log(deltas: np.ndarray, values: np.ndarray, lo: float, hi: float, X: int) -> FitRow:
    mask = (deltas >= lo) & (deltas <= hi)
    x = np.column_stack(
        [
            np.ones(mask.sum()),
            -np.log(deltas[mask]),
            np.log(np.log(1.0 / deltas[mask])),
        ]
    )
    coef, *_ = np.linalg.lstsq(x, np.log(values[mask]), rcond=None)
    pred = x @ coef
    rmse = float(np.sqrt(np.mean((pred - np.log(values[mask])) ** 2)))
    return FitRow(X, lo, hi, float(coef[1]), float(coef[2]), rmse)


def main() -> None:
    node_key = "preasymptotic_log_correction_window_gate"
    attempts = [
        "preasymptotic_log_correction_fisher_wall_gate",
        "finite_cutoff_signature_norm_horizon",
        "critical_point_offset_fisher_metric_mimicry",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:48s} distance={levenshtein(node_key, a)}")
    print("selected=preasymptotic_log_correction_fisher_wall_gate")

    print("\nSTEP 9 missing lemma")
    print(
        "finite-cutoff Fisher wall resolution requires u = delta*log(X) -> infinity; "
        "bounded u gives a pre-asymptotic ceiling."
    )

    Xs = [200, 800, 3200, 12800, 51200]
    us = [0.20, 0.35, 0.60, 1.00, 1.70, 3.00, 5.00, 8.00]
    print("\nCollapse check for normalized ratio R = g_X(delta)*delta^2")
    print("X        u      delta       R_finite   R_continuum  abs_diff")
    for X in Xs:
        logX = math.log(X)
        for u in us:
            delta = u / logX
            if delta >= 0.80:
                continue
            g = finite_fisher(delta, X)
            r = g * delta * delta
            rc = continuum_ratio(u)
            print(f"{X:<8d} {u:4.2f}  {delta:9.5f}  {r:9.5f}  {rc:11.5f}  {abs(r-rc):8.5f}")

    print("\nPower+log fits on finite Fisher cutoffs")
    print("X        window_delta       alpha     beta      rmse")
    windows = [(0.012, 0.055), (0.025, 0.11), (0.050, 0.22), (0.090, 0.36)]
    dense = np.logspace(math.log10(0.010), math.log10(0.40), 90)
    for X in Xs:
        vals = np.array([finite_fisher(float(d), X) for d in dense])
        for lo, hi in windows:
            row = fit_power_log(dense, vals, lo, hi, X)
            print(
                f"{row.X:<8d} [{row.lo:5.3f},{row.hi:5.3f}] "
                f"{row.alpha:+8.4f} {row.beta:+8.4f} {row.rmse:9.5f}"
            )

    print("\nTrue infinite-wall control")
    true_vals = dense ** -2.0
    for lo, hi in windows:
        row = fit_power_log(dense, true_vals, lo, hi, 0)
        print(
            f"X=inf    [{row.lo:5.3f},{row.hi:5.3f}] "
            f"{row.alpha:+8.4f} {row.beta:+8.4f} {row.rmse:9.5f}"
        )

    print("\nInterpretation")
    print(
        "The finite target metric has a clean one-parameter crossover in u=delta*log(X). "
        "This explains the pre-asymptotic drift but also makes the result reducible to "
        "truncated zeta/Fisher asymptotics rather than a new native invariant."
    )


if __name__ == "__main__":
    main()
