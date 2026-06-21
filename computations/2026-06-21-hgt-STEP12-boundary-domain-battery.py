#!/usr/bin/env python3
"""STEP 12 battery: boundary-domain phase sensitivity.

Posted candidate:
    True zeta's phase-increment MSD exponent is more sensitive to sigma-domain
    choice than finite Euler/random controls; lane z-scoring keeps much of the
    sensitivity and within-lane time shuffling kills it.

This battery applies the meaningful scientific-method moves in one run:
    1 split subclaims,
    2 attack as false,
    10 test extreme/right cases,
    12 find invariants,
    13 monotone/cutoff stress,
    22 compare nearby false shuffled statements,
    23 classify boundary cases.
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


def build_fields(
    sigmas: list[float],
    window: tuple[float, float],
    samples: int,
    prime_sets: dict[int, tuple[int, ...]],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    fields: dict[str, np.ndarray] = {
        "true": np.zeros((len(sigmas), samples), dtype=float),
        "random": np.zeros((len(sigmas), samples), dtype=float),
    }
    for n in prime_sets:
        fields[f"finite{n}"] = np.zeros((len(sigmas), samples), dtype=float)
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(np.linspace(window[0], window[1], samples)):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            fields["true"][i, j] = phase_defect(g, zp)
            fields["random"][i, j] = phase_defect(g, rp)
            for n, primes in prime_sets.items():
                fields[f"finite{n}"][i, j] = phase_defect(g, dlog_finite(s, primes))
    return fields


DOMAINS = {
    "left_boundary": [0, 1, 2],
    "critical_core": [1, 2, 3],
    "middle": [2, 3, 4],
    "right": [4, 5, 6],
    "wide": [0, 1, 2, 3, 4, 5, 6],
    "boundary_removed": [1, 2, 3, 4, 5],
}


def fit_alpha(field: np.ndarray) -> float:
    lags = np.asarray([1, 2, 4, 8, 16, 32], dtype=int)
    msd = []
    for lag in lags:
        d = field[:, lag:] - field[:, :-lag]
        msd.append(float(np.mean(d * d)))
    return float(np.polyfit(np.log(lags), np.log(np.maximum(msd, 1e-300)), 1)[0])


def domain_values(field: np.ndarray) -> dict[str, float]:
    return {name: fit_alpha(field[idxs, :]) for name, idxs in DOMAINS.items()}


def range_sd(values: dict[str, float]) -> tuple[float, float]:
    arr = np.asarray(list(values.values()), dtype=float)
    return float(np.max(arr) - np.min(arr)), float(np.std(arr))


def zscore(field: np.ndarray) -> np.ndarray:
    return (field - np.mean(field, axis=1, keepdims=True)) / (np.std(field, axis=1, keepdims=True) + 1e-12)


def shuffled_range(field: np.ndarray, rng: np.random.Generator, reps: int = 8) -> tuple[float, float]:
    vals = []
    for _ in range(reps):
        out = field.copy()
        for i in range(out.shape[0]):
            rng.shuffle(out[i])
        vals.append(range_sd(domain_values(out))[0])
    return float(np.mean(vals)), float(np.max(vals))


def summarize_window(window: tuple[float, float], fields: dict[str, np.ndarray], rng: np.random.Generator, finite_counts: list[int]) -> None:
    true_raw, true_sd = range_sd(domain_values(fields["true"]))
    true_z, true_z_sd = range_sd(domain_values(zscore(fields["true"])))
    true_shuf_mean, true_shuf_max = shuffled_range(fields["true"], rng)
    random_raw, _ = range_sd(domain_values(fields["random"]))
    finite_raws = []
    finite_zs = []
    for n in finite_counts:
        raw, _ = range_sd(domain_values(fields[f"finite{n}"]))
        zr, _ = range_sd(domain_values(zscore(fields[f"finite{n}"])))
        finite_raws.append(raw)
        finite_zs.append(zr)
    max_control = max([random_raw] + finite_raws)
    survives = true_raw > 1.45 * max_control and true_z > 0.15 and true_shuf_max < 0.08
    print(
        f"WINDOW [{window[0]:.0f},{window[1]:.0f}] true_raw={true_raw:.4f} true_z={true_z:.4f} "
        f"true_shuffle_mean={true_shuf_mean:.4f} true_shuffle_max={true_shuf_max:.4f} "
        f"random_raw={random_raw:.4f} max_finite_raw={max(finite_raws):.4f} "
        f"raw_ratio={true_raw / max(max_control,1e-12):.4f} survives={int(survives)}"
    )
    print(
        "FINITE_RAW "
        + " ".join(f"N{n}={v:.4f}" for n, v in zip(finite_counts, finite_raws))
    )
    print(
        "FINITE_ZSCORE "
        + " ".join(f"N{n}={v:.4f}" for n, v in zip(finite_counts, finite_zs))
    )
    vals = domain_values(fields["true"])
    print(
        "TRUE_DOMAIN_ALPHAS "
        + " ".join(f"{name}={vals[name]:.4f}" for name in ["left_boundary", "critical_core", "middle", "right", "wide", "boundary_removed"])
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=320)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211212)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    finite_counts = [30, 80, 160, 240, 400]
    prime_sets = {n: first_primes(n) for n in finite_counts}
    windows = [(14.0, 84.0), (100.0, 170.0), (260.0, 330.0), (500.0, 570.0)]

    print("STEP12 boundary-domain phase sensitivity battery")
    print(f"samples={args.samples} finite_counts={finite_counts}")
    print("survival_rule=true_raw > 1.45*max(finite_raw,random_raw), true_z>0.15, true_shuffle_max<0.08")
    survival_count = 0
    for window in windows:
        fields = build_fields(sigmas, window, args.samples, prime_sets, rng)
        before = survival_count
        summarize_window(window, fields, rng, finite_counts)
        # Repeat the survival calculation here for a machine-readable total.
        true_raw, _ = range_sd(domain_values(fields["true"]))
        true_z, _ = range_sd(domain_values(zscore(fields["true"])))
        true_shuf_mean, true_shuf_max = shuffled_range(fields["true"], rng)
        random_raw, _ = range_sd(domain_values(fields["random"]))
        finite_raws = [range_sd(domain_values(fields[f"finite{n}"]))[0] for n in finite_counts]
        survival_count += int(true_raw > 1.45 * max([random_raw] + finite_raws) and true_z > 0.15 and true_shuf_max < 0.08)
        assert survival_count >= before
    print(f"\nSURVIVAL_WINDOWS {survival_count}/{len(windows)}")
    print("interpretation: robust only if survival holds across several windows and finite cutoff stress stays below true raw domain range.")


if __name__ == "__main__":
    main()
