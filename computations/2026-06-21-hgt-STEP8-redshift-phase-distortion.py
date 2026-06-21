#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase-space distortion dimension.

NODE:
    Redshift-space distortions from peculiar velocities can stretch or compress
    structures and alter inferred clustering dimensions.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_space_distortion_dimension: 20 / 40 = 0.5000
    - C_prime_cutoff_redshift_distortion: 28 / 40 = 0.7000
    - B_zero_shadow_velocity_stretch:    32 / 40 = 0.8000

    Replace a redshift-space point catalog by a sigma/t point cloud of
    phase-defect events for a continuum vertical trace on C. The observed
    coordinate is t' = t + lambda * v_phase(s), where v_phase is the robustly
    normalized local phase velocity of the same analytic component.

STEP 9 method #6:
    Ask what action changes an object. The action is the phase-velocity
    coordinate distortion; the measured object is the correlation dimension of
    high phase-defect events. Promote nothing unless the distortion effect is
    true-specific and not matched by finite or randomized controls.
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


def robust_normalize(x: np.ndarray) -> np.ndarray:
    centered = x - float(np.median(x))
    scale = float(np.quantile(np.abs(centered), 0.90))
    return np.clip(centered / max(scale, 1e-12), -3.0, 3.0)


def field(
    kind: str,
    sigmas: list[float],
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    ts = np.linspace(window[0], window[1], samples)
    sigma_rows: list[np.ndarray] = []
    t_rows: list[np.ndarray] = []
    defect_rows: list[np.ndarray] = []
    velocity_rows: list[np.ndarray] = []
    for sigma in sigmas:
        comps: list[complex] = []
        defects: list[float] = []
        for t in ts:
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            if kind == "true":
                p = dlog_zeta(s)
            elif kind == "finite":
                p = dlog_finite(s, primes)
            elif kind == "random":
                base = dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p = abs(base) * complex(math.cos(theta), math.sin(theta))
            else:
                raise ValueError(kind)
            comps.append(p)
            defects.append(phase_defect(g, p))
        phase = np.unwrap(np.angle(np.asarray(comps, dtype=complex)))
        velocity = robust_normalize(np.gradient(phase, ts))
        sigma_rows.append(np.full(samples, sigma, dtype=float))
        t_rows.append(ts.copy())
        defect_rows.append(np.asarray(defects, dtype=float))
        velocity_rows.append(velocity)
    return (
        np.concatenate(sigma_rows),
        np.concatenate(t_rows),
        np.concatenate(defect_rows),
        np.concatenate(velocity_rows),
    )


def pair_distances(points: np.ndarray) -> np.ndarray:
    n = len(points)
    distances = []
    for i in range(n - 1):
        d = np.linalg.norm(points[i + 1 :] - points[i], axis=1)
        distances.append(d)
    return np.concatenate(distances)


def estimate_dimension(points: np.ndarray) -> tuple[float, float, float]:
    if len(points) < 30:
        return float("nan"), float("nan"), float("nan")
    d = pair_distances(points)
    d = d[d > 1e-12]
    radii = np.geomspace(0.018, 0.55, 24)
    counts = np.asarray([np.mean(d < r) for r in radii], dtype=float)
    mask = (counts > 0.02) & (counts < 0.55)
    if int(np.sum(mask)) < 4:
        return float("nan"), float("nan"), float(np.median(d))
    x = np.log(radii[mask])
    y = np.log(counts[mask])
    coeff = np.polyfit(x, y, 1)
    fit = np.polyval(coeff, x)
    ss_res = float(np.sum((y - fit) ** 2))
    ss_tot = float(np.sum((y - np.mean(y)) ** 2))
    r2 = 1.0 - ss_res / max(ss_tot, 1e-12)
    return float(coeff[0]), r2, float(np.median(d))


def summarize(
    kind: str,
    window: tuple[float, float],
    sigma: np.ndarray,
    t: np.ndarray,
    defect: np.ndarray,
    velocity: np.ndarray,
    strength: float,
) -> dict[str, float]:
    threshold = float(np.quantile(defect, 0.80))
    event = defect >= threshold
    sigma_norm = (sigma[event] - float(np.min(sigma))) / max(float(np.max(sigma) - np.min(sigma)), 1e-12)
    t_norm = (t[event] - window[0]) / (window[1] - window[0])
    base_points = np.column_stack([sigma_norm, t_norm])
    distorted_points = np.column_stack([sigma_norm, t_norm + strength * velocity[event]])
    base_d, base_r2, base_med = estimate_dimension(base_points)
    distorted_d, distorted_r2, distorted_med = estimate_dimension(distorted_points)
    return {
        "threshold": threshold,
        "events": float(int(np.sum(event))),
        "base_d": base_d,
        "distorted_d": distorted_d,
        "delta": distorted_d - base_d,
        "base_r2": base_r2,
        "distorted_r2": distorted_r2,
        "base_med": base_med,
        "distorted_med": distorted_med,
        "velocity_iqr": float(np.quantile(velocity[event], 0.75) - np.quantile(velocity[event], 0.25)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--prime-count", type=int, default=150)
    args = parser.parse_args()
    rng = np.random.default_rng(2606210606)
    primes = first_primes(args.prime_count)
    sigmas = [0.3, 0.5, 0.7, 0.9, 1.2]
    windows = [(100.0, 170.0), (500.0, 570.0)]
    strengths = [0.04, 0.08, 0.14, 0.22]

    print("STEP8/9 phase-space distortion dimension")
    print(f"samples={args.samples} prime_count={args.prime_count} method=6 action_changes_object")
    print("threshold=within-kind q80 phase-defect event cloud")
    print("kind window strength events threshold base_D distorted_D delta_D base_r2 distorted_r2 base_median distorted_median velocity_iqr")
    for window in windows:
        for kind in ["true", "finite", "random"]:
            sigma, t, defect, velocity = field(kind, sigmas, window, args.samples, primes, rng)
            for strength in strengths:
                row = summarize(kind, window, sigma, t, defect, velocity, strength)
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {strength:.2f} "
                    f"{int(row['events']):4d} {row['threshold']:.6g} "
                    f"{row['base_d']:.4f} {row['distorted_d']:.4f} {row['delta']:+.4f} "
                    f"{row['base_r2']:.4f} {row['distorted_r2']:.4f} "
                    f"{row['base_med']:.4f} {row['distorted_med']:.4f} {row['velocity_iqr']:.4f}"
                )
    print("\nreduction gate")
    print("Promote nothing if dimension shifts are estimator/coordinate artifacts also present in finite or randomized controls.")


if __name__ == "__main__":
    main()
