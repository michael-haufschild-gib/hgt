#!/usr/bin/env python3
"""NODE test: finite-data Hurst estimation is artifact-sensitive.

NODE:
    Estimating H from finite data is highly sensitive to trends,
    nonstationarity, aggregation, and measurement noise.

Constraint:
    A fitted Hurst exponent is interpretable only after finite-sample window,
    trend, nonstationarity, aggregation, and measurement-noise gates are fixed.
"""

from __future__ import annotations

import numpy as np


SEED = 20260621
N = 512
REPS = 180
TRUE_H = 0.70


def fgn_cov(n: int, h: float) -> np.ndarray:
    k = np.arange(n, dtype=float)
    cov = np.ones(n, dtype=float)
    m = k > 0
    km = k[m]
    cov[m] = 0.5 * ((km + 1.0) ** (2.0 * h) - 2.0 * km ** (2.0 * h) + (km - 1.0) ** (2.0 * h))
    return cov


def sample_fbm_paths(rng: np.random.Generator, n: int, h: float, reps: int) -> np.ndarray:
    cov_by_dist = fgn_cov(n, h)
    idx = np.arange(n)
    cov = cov_by_dist[np.abs(idx[:, None] - idx[None, :])]
    cov.flat[:: n + 1] += 1e-9
    fgn = rng.multivariate_normal(np.zeros(n), cov, size=reps)
    return np.cumsum(fgn, axis=1)


def estimate_h_variogram(paths: np.ndarray, lags: np.ndarray) -> np.ndarray:
    out = []
    for path in paths:
        vars_ = []
        used = []
        for lag in lags:
            if lag >= path.size // 2:
                continue
            diff = path[lag:] - path[:-lag]
            vars_.append(float(np.var(diff)))
            used.append(lag)
        slope = np.polyfit(np.log(used), np.log(np.maximum(vars_, 1e-300)), 1)[0]
        out.append(0.5 * float(slope))
    return np.asarray(out, dtype=float)


def aggregate_path(path: np.ndarray, block: int) -> np.ndarray:
    usable = (len(path) // block) * block
    return path[:usable].reshape(-1, block).mean(axis=1)


def summarize(label: str, paths: np.ndarray, lags: np.ndarray) -> None:
    hhat = estimate_h_variogram(paths, lags)
    q10, q50, q90 = np.quantile(hhat, [0.10, 0.50, 0.90])
    print(
        f"{label:22s} median={q50:.4f} mean={float(np.mean(hhat)):.4f} "
        f"sd={float(np.std(hhat)):.4f} q10={q10:.4f} q90={q90:.4f} "
        f"bias_med={q50 - TRUE_H:+.4f}"
    )


def main() -> None:
    rng = np.random.default_rng(SEED)
    clean = sample_fbm_paths(rng, N, TRUE_H, REPS)
    t = np.linspace(-0.5, 0.5, N)
    path_sd = float(np.std(clean[:, -1] - clean[:, 0]))
    lags = np.asarray([1, 2, 4, 8, 16, 32, 64], dtype=int)

    curved_trend = clean + (2.40 * path_sd) * (t[None, :] ** 2 - np.mean(t**2))
    level_shift = clean.copy()
    level_shift[:, N // 2 :] += 0.65 * path_sd
    noisy = clean + rng.normal(0.0, 0.40 * float(np.std(np.diff(clean, axis=1))), size=clean.shape)
    aggregated4 = np.asarray([aggregate_path(path, 4) for path in clean])
    mixed = noisy + (1.60 * path_sd) * (t[None, :] ** 2 - np.mean(t**2))

    print("NODE: Hurst estimation sensitivity under finite data artifacts")
    print(f"seed={SEED} n={N} reps={REPS} true_H={TRUE_H}")
    print("estimator=variogram_slope_over_lags")
    summarize("clean_fbm", clean, lags)
    summarize("curved_trend", curved_trend, lags)
    summarize("level_shift", level_shift, lags)
    summarize("measurement_noise", noisy, lags)
    summarize("aggregate_block4", aggregated4, np.asarray([1, 2, 4, 8, 16, 32], dtype=int))
    summarize("curved_trend_noise", mixed, lags)

    print("\nartifact sweep: measurement noise sd as fraction of increment sd")
    inc_sd = float(np.std(np.diff(clean, axis=1)))
    for frac in [0.0, 0.1, 0.2, 0.4, 0.8, 1.2]:
        perturbed = clean + rng.normal(0.0, frac * inc_sd, size=clean.shape)
        hhat = estimate_h_variogram(perturbed, lags)
        print(f"noise_frac={frac:.1f} median_H={float(np.median(hhat)):.4f} sd={float(np.std(hhat)):.4f}")

    print("\ncriterion")
    print("If clean, trend, level-shift, noise, and aggregation estimates differ at fixed true H, finite-data H is a conditional statistic, not a mechanism.")


if __name__ == "__main__":
    main()
