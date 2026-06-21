#!/usr/bin/env python3
"""NODE test: short-range vs long-range associated fields.

NODE:
    The difference between short-range associated fields and long-range
    dependent associated fields, which may have nonstandard limits.

Constraint:
    Positive association alone is not enough for a standard CLT. Covariance
    summability decides whether Var(S_n) is order n or larger.
"""

from __future__ import annotations

import numpy as np


SEED = 20260621


def fgn_cov(k: np.ndarray, h: float) -> np.ndarray:
    out = np.ones_like(k, dtype=float)
    mask = k > 0
    km = k[mask].astype(float)
    out[mask] = 0.5 * ((km + 1.0) ** (2.0 * h) - 2.0 * km ** (2.0 * h) + (km - 1.0) ** (2.0 * h))
    return out


def cov_values(n: int, case: str) -> np.ndarray:
    ks = np.arange(0, n, dtype=int)
    if case == "short_ar1":
        return 0.40 ** ks
    if case == "long_fgn_H0.8":
        return fgn_cov(ks, 0.8)
    raise ValueError(case)


def var_sum(n: int, case: str) -> float:
    ks = np.arange(1, n, dtype=float)
    cov = cov_values(n, case)[1:]
    return float(n + 2.0 * np.sum((n - ks) * cov))


def toeplitz_cov(n: int, case: str) -> np.ndarray:
    idx = np.arange(n)
    dist = np.abs(idx[:, None] - idx[None, :])
    cov_by_dist = cov_values(n, case)
    cov = cov_by_dist[dist]
    cov.flat[:: n + 1] += 1e-9
    return cov


def simulate_sums(rng: np.random.Generator, n: int, case: str, reps: int = 1200) -> tuple[float, float, float]:
    cov = toeplitz_cov(n, case)
    vals = rng.multivariate_normal(np.zeros(n), cov, size=reps).sum(axis=1)
    return float(np.var(vals)), float(np.mean(vals / np.sqrt(n))), float(np.std(vals / np.sqrt(n)))


def main() -> None:
    rng = np.random.default_rng(SEED)
    cases = [
        ("short_ar1", "short_ar1", 1.0),
        ("long_fgn_H0.8", "long_fgn_H0.8", 1.6),
    ]
    ns = [64, 128, 256, 512, 1024, 2048, 4096]
    print("NODE: short-range vs long-range associated Gaussian fields")
    print(f"seed={SEED}")
    print("case n VarS VarS/n VarS/nonstandard_norm standard_sqrt_gate")
    for name, case, exponent in cases:
        for n in ns:
            v = var_sum(n, case)
            print(
                f"{name:16s} {n:5d} {v:12.4f} {v/n:10.4f} "
                f"{v/(n**exponent):22.4f} {int(exponent == 1.0)}"
            )
    print("\nSIMULATION CHECK n=512")
    print("case empirical_VarS analytic_VarS sqrt_norm_std")
    for name, case, _ in cases:
        emp_var, _, sqrt_std = simulate_sums(rng, 512, case)
        print(f"{name:16s} {emp_var:14.4f} {var_sum(512, case):14.4f} {sqrt_std:14.4f}")
    print("\ninterpretation")
    print("Short-range associated fields keep Var(S_n)/n bounded. Long-range fields make sqrt(n)-normalized variance grow, so a standard CLT normalization is the wrong gate.")


if __name__ == "__main__":
    main()
