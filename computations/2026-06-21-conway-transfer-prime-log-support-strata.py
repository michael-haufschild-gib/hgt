#!/usr/bin/env python3
"""
Attempt 6 transfer experiment.

ResearchNode: value apex / degree-2 prime-log corank.
NODE constraint: pooled rare-event estimates can hide stratum-specific effects.

Transfer:
  In a finite degree-2 prime-log relation search, pool all monomials and compare
  the residual minimum against support-size strata (squares vs cross terms).
  The goal is not to infer relations; it is to test whether pooled residual
  summaries are dominated by stratum/dimension effects.
"""

from __future__ import annotations

from math import log, sqrt

import numpy as np


def monomials_degree2(values: list[float]) -> tuple[list[str], np.ndarray, list[int]]:
    names: list[str] = []
    vals: list[float] = []
    supports: list[int] = []
    for i, x in enumerate(values):
        for j, y in enumerate(values[i:], start=i):
            names.append(f"L{i+1}L{j+1}")
            vals.append(x * y)
            supports.append(1 if i == j else 2)
    return names, np.array(vals, dtype=float), supports


def random_residuals(vals: np.ndarray, n_samples: int, height: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    dim = len(vals)
    coeffs = rng.integers(-height, height + 1, size=(n_samples, dim))
    nonzero = np.any(coeffs != 0, axis=1)
    coeffs = coeffs[nonzero]
    numer = np.abs(coeffs @ vals)
    denom = np.linalg.norm(coeffs, axis=1) * np.linalg.norm(vals)
    return numer / denom


def summarize(label: str, vals: np.ndarray, n_samples: int, height: int, seed: int) -> tuple[float, float]:
    residuals = random_residuals(vals, n_samples=n_samples, height=height, seed=seed)
    q01 = float(np.quantile(residuals, 0.01))
    mn = float(np.min(residuals))
    print(f"  {label:12s}: dim={len(vals)}, min={mn:.3e}, q01={q01:.3e}")
    return mn, q01


def run_case(label: str, base_values: list[float], seed: int) -> None:
    names, vals, supports = monomials_degree2(base_values)
    print(label)
    print(f"  monomials={names}")
    pooled = vals
    squares = np.array([v for v, s in zip(vals, supports) if s == 1])
    crosses = np.array([v for v, s in zip(vals, supports) if s == 2])
    summarize("pooled", pooled, n_samples=200000, height=12, seed=seed)
    summarize("squares", squares, n_samples=200000, height=12, seed=seed + 1)
    summarize("crosses", crosses, n_samples=200000, height=12, seed=seed + 2)
    print()


def planted_case(seed: int) -> None:
    # Values with an exact square-stratum relation: v0 - 2*v1 = 0.
    vals = np.array([2.0, 1.0, sqrt(3.0), log(2.0), log(3.0), log(5.0)])
    print("planted control with exact relation in first two coordinates")
    summarize("pooled", vals, n_samples=200000, height=12, seed=seed)
    summarize("planted", vals[:2], n_samples=200000, height=12, seed=seed + 1)
    summarize("rest", vals[2:], n_samples=200000, height=12, seed=seed + 2)
    print()


def main() -> None:
    print("POOLED VS SUPPORT-STRATIFIED DEGREE-2 PRIME-LOG RESIDUALS")
    print("constants are log 2, log 3, log 5; no zeta(n) values are used")
    print()
    run_case("actual prime logs", [log(2.0), log(3.0), log(5.0)], seed=101)
    rng = np.random.default_rng(44)
    generic_control = list(rng.uniform(0.6, 1.8, size=3))
    run_case("generic real control", generic_control, seed=201)
    planted_case(seed=301)


if __name__ == "__main__":
    main()
