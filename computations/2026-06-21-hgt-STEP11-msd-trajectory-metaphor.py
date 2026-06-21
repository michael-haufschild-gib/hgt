#!/usr/bin/env python3
"""THE-MACHINE Step 11 metaphor experiment: same skyline, different rooms.

Metaphor:
    An ensemble MSD is a skyline: it can look smooth while the rooms inside
    the building have incompatible strains. The constraint is not the skyline
    curve; it is whether the rooms self-average.

Wild experiment:
    Build Fourier-phase surrogates of the continuum phase-defect trace. These
    nearly preserve the global MSD/autocorrelation constraint but rearrange the
    local rooms. Then test whether per-window time-averaged MSD heterogeneity
    is forced by the global curve or can move independently.

Scientific method #11:
    Run experiments.
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
    out = {"true": [], "finite": [], "random": []}
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        true_p = dlog_zeta(s)
        finite_p = dlog_finite(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        random_p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        out["true"].append(phase_defect(g, true_p))
        out["finite"].append(phase_defect(g, finite_p))
        out["random"].append(phase_defect(g, random_p))
    return {k: np.asarray(v, dtype=float) for k, v in out.items()}


def windows(vals: np.ndarray, window_len: int, stride: int) -> np.ndarray:
    return np.asarray([vals[i : i + window_len] for i in range(0, len(vals) - window_len + 1, stride)], dtype=float)


def ensemble_msd_from_windows(w: np.ndarray, lags: np.ndarray) -> np.ndarray:
    return np.asarray([float(np.mean((w[:, lag:] - w[:, :-lag]) ** 2)) for lag in lags], dtype=float)


def metrics(vals: np.ndarray, window_len: int = 64, stride: int = 16) -> dict[str, np.ndarray | float]:
    w = windows(vals, window_len, stride)
    lags = np.asarray([1, 2, 4, 8, 16], dtype=int)
    emsd = ensemble_msd_from_windows(w, lags)
    ta_lag = 8
    tam = np.mean((w[:, ta_lag:] - w[:, :-ta_lag]) ** 2, axis=1)
    q10, q90 = np.quantile(tam, [0.10, 0.90])
    eb = float(np.var(tam) / (np.mean(tam) ** 2 + 1e-300))
    return {
        "emsd": emsd,
        "eb": eb,
        "q90_q10": float(q90 / max(q10, 1e-300)),
        "outside_factor2": float(np.mean((tam < np.mean(tam) / 2.0) | (tam > 2.0 * np.mean(tam)))),
    }


def fourier_phase_surrogate(vals: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    centered = vals - float(np.mean(vals))
    spec = np.fft.rfft(centered)
    if len(spec) > 2:
        phases = rng.uniform(0.0, 2.0 * math.pi, size=len(spec) - 2)
        spec[1:-1] = np.abs(spec[1:-1]) * np.exp(1j * phases)
    return np.fft.irfft(spec, n=len(vals)) + float(np.mean(vals))


def rank_remap(source: np.ndarray, target_distribution: np.ndarray) -> np.ndarray:
    order = np.argsort(source, kind="mergesort")
    sorted_target = np.sort(target_distribution)
    out = np.zeros_like(source, dtype=float)
    out[order] = sorted_target
    return out


def compare(original: np.ndarray, surrogate: np.ndarray) -> dict[str, float]:
    m0 = metrics(original)
    m1 = metrics(surrogate)
    msd0 = m0["emsd"]
    msd1 = m1["emsd"]
    rel = float(np.linalg.norm(msd1 - msd0) / (np.linalg.norm(msd0) + 1e-300))
    eb_ratio = float(m1["eb"] / max(float(m0["eb"]), 1e-300))
    q_ratio = float(m1["q90_q10"] / max(float(m0["q90_q10"]), 1e-300))
    same_msd_diff_rooms = rel < 0.08 and (eb_ratio < 0.70 or eb_ratio > 1.30 or q_ratio < 0.70 or q_ratio > 1.30)
    return {
        "msd_rel": rel,
        "orig_eb": float(m0["eb"]),
        "sur_eb": float(m1["eb"]),
        "eb_ratio": eb_ratio,
        "orig_q": float(m0["q90_q10"]),
        "sur_q": float(m1["q90_q10"]),
        "q_ratio": q_ratio,
        "same_msd_diff_rooms": 1.0 if same_msd_diff_rooms else 0.0,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211111)
    primes = first_primes(args.prime_count)
    print("STEP11 phase-MSD metaphor experiment")
    print(f"samples={args.samples} prime_count={args.prime_count} method=11 run_experiments")
    print("kind sigma height_window surrogate msd_rel orig_EB sur_EB EB_ratio orig_q90q10 sur_q90q10 q_ratio same_msd_diff_rooms")

    for sigma in [0.3, 0.5, 1.2]:
        for height_window in [(100.0, 170.0), (500.0, 570.0)]:
            bundle = trace_bundle(sigma, height_window, args.samples, primes, rng)
            for kind in ["true", "finite", "random"]:
                original = bundle[kind]
                fourier = fourier_phase_surrogate(original, rng)
                rank_fourier = rank_remap(fourier, original)
                for label, surrogate in [("fourier", fourier), ("rank_fourier", rank_fourier)]:
                    row = compare(original, surrogate)
                    print(
                        f"{kind:6s} {sigma:.1f} [{height_window[0]:.0f},{height_window[1]:.0f}] {label:12s} "
                        f"{row['msd_rel']:.4f} {row['orig_eb']:.4f} {row['sur_eb']:.4f} "
                        f"{row['eb_ratio']:.4f} {row['orig_q']:.4f} {row['sur_q']:.4f} "
                        f"{row['q_ratio']:.4f} {int(row['same_msd_diff_rooms'])}"
                    )

    print("\ninterpretation gate")
    print("If true and controls both admit same-MSD/different-room surrogates, the metaphor is generic and reduces to MSD/autocorrelation insufficiency.")


if __name__ == "__main__":
    main()
