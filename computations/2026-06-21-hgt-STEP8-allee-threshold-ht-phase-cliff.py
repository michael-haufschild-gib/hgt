#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for the Allee-threshold NODE.

NODE constraint:
    A threshold can turn extinction risk into a cliff-like function of abundance.

Step 8 transfer rule:
    Three wildly different continuum/differential HT attempts are ranked by
    Levenshtein distance. Continue only with the lowest-distance attempt.

Step 9 method #13:
    Find a monotone quantity. Here: as the Allee-like phase threshold rises,
    extinction risk should be monotone nondecreasing. The scientific question is
    whether the resulting threshold cliff is HT-native or just the already-known
    phase-defect/run-persistence observable.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


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
    runs: list[int] = []
    current = 0
    for item in mask:
        if bool(item):
            current += 1
        elif current:
            runs.append(current)
            current = 0
    if current:
        runs.append(current)
    return runs


def extinction_risk(defects: np.ndarray, threshold: float, depth: int) -> dict[str, float]:
    above = defects > threshold
    runs = run_lengths(above)
    if not runs:
        return {
            "occupancy": 0.0,
            "entry_rate": 0.0,
            "median_run": 0.0,
            "max_run": 0.0,
            "survive_depth": 0.0,
            "extinction_risk": 1.0,
        }
    survive = float(np.mean([r >= depth for r in runs]))
    return {
        "occupancy": float(np.mean(above)),
        "entry_rate": float(len(runs) / max(1, len(defects))),
        "median_run": float(np.median(runs)),
        "max_run": float(max(runs)),
        "survive_depth": survive,
        "extinction_risk": 1.0 - survive,
    }


def defect_panel(sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> dict[str, np.ndarray]:
    true_vals: list[float] = []
    finite_vals: list[float] = []
    amp_match_vals: list[float] = []
    random_vals: list[float] = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p_true = dlog_zeta(s)
        p_finite = dlog_finite_euler(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        p_random = abs(p_true) * complex(math.cos(theta), math.sin(theta))
        p_amp_match = p_finite * (abs(p_true) / (abs(p_finite) + 1e-300))
        true_vals.append(max(0.0, phase_defect(g, p_true)))
        finite_vals.append(max(0.0, phase_defect(g, p_finite)))
        amp_match_vals.append(max(0.0, phase_defect(g, p_amp_match)))
        random_vals.append(max(0.0, phase_defect(g, p_random)))
    return {
        "true": np.asarray(true_vals),
        "finite": np.asarray(finite_vals),
        "ampmatched-finite": np.asarray(amp_match_vals),
        "random-phase": np.asarray(random_vals),
    }


def monotone_violations(vals: list[float]) -> int:
    return sum(1 for a, b in zip(vals, vals[1:]) if b + 1e-12 < a)


def max_jump(vals: list[float]) -> float:
    return max(abs(b - a) for a, b in zip(vals, vals[1:])) if len(vals) > 1 else 0.0


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--depth", type=int, default=16)
    args = parser.parse_args()

    kernel = "allee threshold extinction risk discontinuous nonlinear abundance absorbing boundary"
    attempts = {
        "phase-defect-allee-threshold": "allee threshold phase defect abundance extinction risk discontinuous nonlinear absorbing boundary",
        "zero-tube-critical-front": "zero proximity tube critical front absorbing boundary around zeros",
        "finite-prime-rescue-noise": "finite prime rescue immigration cutoff stochastic noise suppresses extinction",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:30s} distance={dist}")
    print(f"selected={selected}")
    if selected != "phase-defect-allee-threshold":
        raise SystemExit("Selected attempt is not implemented in this script.")

    print("\nSTEP9 method #13: find a monotone quantity")
    print(f"samples={args.samples} finite_prime_count={args.prime_count} survival_depth={args.depth}")
    print(
        "kind sigma window threshold occupancy entry_rate median_run max_run "
        "survive_depth extinction_risk"
    )
    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(20260621)
    thresholds = [0.0, 0.05, 0.10, 0.20, 0.35, 0.50]
    cases = [
        (0.3, (100.0, 170.0)),
        (0.5, (100.0, 170.0)),
        (0.7, (100.0, 170.0)),
        (1.2, (100.0, 170.0)),
        (0.3, (500.0, 570.0)),
    ]
    summary: list[tuple[str, float, tuple[float, float], list[float]]] = []
    for sigma, window in cases:
        panel = defect_panel(sigma, window, args.samples, primes, rng)
        for kind, defects in panel.items():
            risks = []
            for threshold in thresholds:
                row = extinction_risk(defects, threshold, args.depth)
                risks.append(row["extinction_risk"])
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} "
                    f"{row['occupancy']:.3f} {row['entry_rate']:.3f} {row['median_run']:.1f} "
                    f"{row['max_run']:.0f} {row['survive_depth']:.3f} {row['extinction_risk']:.3f}"
                )
            summary.append((kind, sigma, window, risks))

    print("\nMonotone-threshold summary")
    print("kind sigma window violations max_adjacent_risk_jump risks")
    for kind, sigma, window, risks in summary:
        print(
            f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
            f"{monotone_violations(risks):10d} {max_jump(risks):22.3f} "
            f"{','.join(f'{x:.3f}' for x in risks)}"
        )

    print(
        "\nInterpretation key: a non-reducing result would need a threshold cliff not "
        "explained by the already-posted phase-carrier/run-lifetime facts and not "
        "reproduced by amplitude-matched finite or random-phase controls."
    )


if __name__ == "__main__":
    main()
