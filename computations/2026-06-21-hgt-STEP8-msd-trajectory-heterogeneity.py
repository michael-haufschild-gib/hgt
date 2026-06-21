#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase-MSD trajectory heterogeneity.

NODE:
    Mean squared displacement can misclassify transport when
    trajectory-level heterogeneity is ignored.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_msd_trajectory_heterogeneity:         6 / 34 = 0.1765
    - B_log_derivative_displacement_heterogeneity: 22 / 41 = 0.5366
    - C_zero_shadow_transport_misclassification:   29 / 39 = 0.7436

    Replace stochastic transport trajectories by short vertical trace windows
    in the continuum variable s = sigma + it. The observable is the phase
    defect of the archimedean-prime differential weld,

        Delta(s)=max(log|Gamma_infty|, log|P|)-log|Gamma_infty+P|.

    The test asks whether an ensemble MSD-like curve of Delta increments hides
    heterogeneous per-window time-averaged MSD.

STEP 9 method #9:
    Test small cases. Use short traces, small windows, and the first few
    sigma/window regimes before treating any apparent signal as structural.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def first_primes(n: int) -> tuple[int, ...]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def trace_bundle(
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    true_vals: list[float] = []
    finite_vals: list[float] = []
    random_vals: list[float] = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        true_p = dlog_zeta(s)
        finite_p = dlog_finite(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        random_p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        true_vals.append(phase_defect(g, true_p))
        finite_vals.append(phase_defect(g, finite_p))
        random_vals.append(phase_defect(g, random_p))
    return {
        "true": np.asarray(true_vals, dtype=float),
        "finite": np.asarray(finite_vals, dtype=float),
        "random": np.asarray(random_vals, dtype=float),
    }


def make_windows(vals: np.ndarray, window_len: int, stride: int) -> np.ndarray:
    rows = []
    for start in range(0, len(vals) - window_len + 1, stride):
        rows.append(vals[start : start + window_len])
    return np.asarray(rows, dtype=float)


def ensemble_msd(windows: np.ndarray, lags: np.ndarray) -> np.ndarray:
    out = []
    for lag in lags:
        disp = windows[:, lag:] - windows[:, :-lag]
        out.append(float(np.mean(disp * disp)))
    return np.asarray(out, dtype=float)


def time_avg_msd(windows: np.ndarray, lag: int) -> np.ndarray:
    disp = windows[:, lag:] - windows[:, :-lag]
    return np.mean(disp * disp, axis=1)


def fit_alpha(lags: np.ndarray, msd: np.ndarray) -> float:
    safe = np.maximum(msd, 1e-300)
    return float(np.polyfit(np.log(lags), np.log(safe), 1)[0])


def summarize(vals: np.ndarray, window_len: int, stride: int) -> dict[str, float | str]:
    windows = make_windows(vals, window_len, stride)
    lags = np.asarray([lag for lag in [1, 2, 4, 8, 16] if lag < window_len // 2], dtype=int)
    emsd = ensemble_msd(windows, lags)
    ta_lag = int(lags[-2] if len(lags) > 2 else lags[-1])
    tam = time_avg_msd(windows, ta_lag)
    alpha = fit_alpha(lags, emsd)
    eb = float(np.var(tam) / (np.mean(tam) ** 2 + 1e-300))
    q10, q50, q90 = np.quantile(tam, [0.10, 0.50, 0.90])
    ensemble_at_lag = float(emsd[lags == ta_lag][0])
    outside_factor2 = float(np.mean((tam < ensemble_at_lag / 2.0) | (tam > 2.0 * ensemble_at_lag)))
    hidden = (eb > 0.35 or (q90 / max(q10, 1e-300)) > 4.0 or outside_factor2 > 0.25) and -0.25 <= alpha <= 2.25
    return {
        "n_windows": float(windows.shape[0]),
        "ta_lag": float(ta_lag),
        "alpha": alpha,
        "emsd_talag": ensemble_at_lag,
        "ta_mean": float(np.mean(tam)),
        "ta_median": float(q50),
        "q90_q10": float(q90 / max(q10, 1e-300)),
        "eb": eb,
        "outside_factor2": outside_factor2,
        "hidden_heterog": "yes" if hidden else "no",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=384)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    rng = np.random.default_rng(2606210909)
    primes = first_primes(args.prime_count)
    print("STEP8/9 phase-MSD trajectory heterogeneity")
    print(f"samples={args.samples} prime_count={args.prime_count}")
    print("method=9 test_small_cases")
    print("kind sigma height_window small_window n_windows ta_lag alpha emsd_talag ta_median q90/q10 EB outside_factor2 hidden_heterog")

    for sigma in [0.3, 0.5, 1.2]:
        for height_window in [(100.0, 170.0), (500.0, 570.0)]:
            bundle = trace_bundle(sigma, height_window, args.samples, primes, rng)
            for small_window in [32, 64]:
                stride = small_window // 2
                for kind in ["true", "finite", "random"]:
                    row = summarize(bundle[kind], small_window, stride)
                    print(
                        f"{kind:6s} {sigma:.1f} [{height_window[0]:.0f},{height_window[1]:.0f}] "
                        f"{small_window:3d} {row['n_windows']:.0f} {row['ta_lag']:.0f} "
                        f"{row['alpha']:.4f} {row['emsd_talag']:.6g} {row['ta_median']:.6g} "
                        f"{row['q90_q10']:.4f} {row['eb']:.4f} {row['outside_factor2']:.4f} "
                        f"{row['hidden_heterog']}"
                    )

    print("\nreduction gate")
    print("A candidate is not HT-specific if finite Euler or random-phase controls show the same hidden-heterogeneity pattern in the same small cases.")


if __name__ == "__main__":
    main()
