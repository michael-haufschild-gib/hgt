#!/usr/bin/env python3
"""THE-MACHINE run: kinetic proofreading off-rate dominance.

NODE:
    On-rate differences usually contribute much less than off-rate differences.

Constraint:
    In kinetic proofreading, entry/on-rate affects initial capture once, while
    ligand lifetime/off-rate is tested repeatedly by irreversible forward
    steps. Thus specificity grows mainly with survival through repeated
    dissociation chances.

STEP 9 method #17:
    Change representation. On the HT side, represent the phase-carrier defect
    not by pointwise magnitude but by lifetimes of positive phase-defect runs.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def proofreading_specificity(kon_ratio: float, koff_good: float, koff_bad: float, forward: float, depth: int) -> float:
    good_survival = (forward / (forward + koff_good)) ** depth
    bad_survival = (forward / (forward + koff_bad)) ** depth
    return kon_ratio * good_survival / max(bad_survival, 1e-300)


def node_simulation() -> None:
    print("NODE simulation: kinetic proofreading amplifies off-rate/lifetime more than on-rate")
    print("depth onrate_only offrate_only both")
    for depth in [0, 1, 2, 4, 8, 12]:
        onrate_only = proofreading_specificity(4.0, koff_good=1.0, koff_bad=1.0, forward=1.0, depth=depth)
        offrate_only = proofreading_specificity(1.0, koff_good=0.2, koff_bad=1.0, forward=1.0, depth=depth)
        both = proofreading_specificity(4.0, koff_good=0.2, koff_bad=1.0, forward=1.0, depth=depth)
        print(f"{depth:5d} {onrate_only:11.5g} {offrate_only:12.5g} {both:12.5g}")
    print("boundary: depth=0 preserves only on-rate; increasing depth exponentially amplifies off-rate ratio")


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = cur
    return prev[-1]


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


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def run_lengths(mask: np.ndarray) -> list[int]:
    out: list[int] = []
    current = 0
    for val in mask:
        if bool(val):
            current += 1
        elif current:
            out.append(current)
            current = 0
    if current:
        out.append(current)
    return out


def survival_metrics(defects: np.ndarray, threshold: float) -> dict[str, float]:
    good = defects > threshold
    runs = run_lengths(good)
    entries = len(runs)
    exits = max(0, entries - (1 if good[-1] else 0))
    good_count = int(np.sum(good))
    out = {
        "occupancy": float(np.mean(good)),
        "entry_rate": float(entries / max(1, len(good))),
        "off_hazard": float(exits / max(1, good_count)),
        "median_run": float(np.median(runs)) if runs else 0.0,
        "max_run": float(max(runs)) if runs else 0.0,
    }
    for depth in [2, 4, 8, 16, 32]:
        out[f"survive_{depth}"] = float(np.mean([r >= depth for r in runs])) if runs else 0.0
    return out


def defects_for(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(phase_defect(g, p))
    return np.asarray(vals, dtype=float)


def ht_lifetime_run(samples: int, prime_count: int, threshold: float) -> None:
    kernel = "kon capture koff dissociation repeated survival depth specificity"
    attempts = {
        "A_antiphase_run_lifetime": "capture phase-defect run dissociation termination repeated survival depth specificity",
        "B_amplitude_threshold_depth": "capture amplitude threshold magnitude repeated cutoff depth specificity",
        "C_zero_tube_dwell_time": "capture zero proximity dwell tube escape repeated depth specificity",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:28s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    rng = np.random.default_rng(260621)
    windows = [(100.0, 170.0), (500.0, 570.0), (14.0, 84.0)]
    sigmas = [0.3, 0.5, 0.7, 1.2]
    print("\nSTEP8/9 HT transfer: phase-defect lifetime representation")
    print(f"samples={samples} finite_prime_count={prime_count} threshold={threshold}")
    print(
        "kind sigma window occupancy entry_rate off_hazard median_run max_run "
        "survive_2 survive_4 survive_8 survive_16 survive_32"
    )
    for window in windows:
        for sigma in sigmas:
            for kind in ["true", "finite", "random"]:
                defects = defects_for(kind, sigma, window, samples, primes, rng)
                row = survival_metrics(defects, threshold)
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{row['occupancy']:.3f} {row['entry_rate']:.3f} {row['off_hazard']:.4f} "
                    f"{row['median_run']:.1f} {row['max_run']:.0f} "
                    f"{row['survive_2']:.3f} {row['survive_4']:.3f} {row['survive_8']:.3f} "
                    f"{row['survive_16']:.3f} {row['survive_32']:.3f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=280)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=0.0)
    args = parser.parse_args()
    node_simulation()
    ht_lifetime_run(args.samples, args.prime_count, args.threshold)


if __name__ == "__main__":
    main()
