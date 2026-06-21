#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for crisis laminar power-law scaling.

NODE constraint:
    Mean laminar duration follows a power law with distance from the crisis
    parameter.

Step 8:
    Create three HT transfer attempts and select the lowest-Levenshtein one.

Step 9 method #16:
    Use a minimal counterexample. If the apparent scaling survives only because
    of thresholding a one-dimensional distribution, a shuffled-value series is
    the minimal counterexample to any phase-geometry claim.
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
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
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
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def profile(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        true_p = dlog_zeta(s)
        finite_p = dlog_finite_euler(s, primes)
        if kind == "true":
            p = true_p
        elif kind == "finite":
            p = finite_p
        elif kind == "ampmatched-finite":
            p = finite_p * (abs(true_p) / (abs(finite_p) + 1e-300))
        elif kind == "random-phase":
            theta = float(rng.uniform(-math.pi, math.pi))
            p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        elif kind == "gamma-only":
            p = 0.0 + 0.0j
        else:
            raise ValueError(kind)
        vals.append(phase_defect(g, p))
    return np.asarray(vals)


def laminar_runs(mask: np.ndarray) -> list[int]:
    # mask=True means burst; laminar runs are False intervals.
    runs: list[int] = []
    current = 0
    for is_burst in mask:
        if is_burst:
            if current:
                runs.append(current)
                current = 0
        else:
            current += 1
    if current:
        runs.append(current)
    return runs


def fit_power(distances: np.ndarray, means: np.ndarray) -> tuple[float, float]:
    ok = np.isfinite(means) & (means > 0)
    if np.sum(ok) < 3:
        return float("nan"), float("nan")
    x = np.log(distances[ok])
    y = np.log(means[ok])
    slope, intercept = np.polyfit(x, y, 1)
    pred = slope * x + intercept
    ss_res = float(np.sum((y - pred) ** 2))
    ss_tot = float(np.sum((y - np.mean(y)) ** 2))
    return float(-slope), float(1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0)


def scaling(vals: np.ndarray, quantiles: list[float]) -> dict[str, object]:
    distances = np.asarray([1.0 - q for q in quantiles])
    means = []
    counts = []
    for q in quantiles:
        threshold = float(np.quantile(vals, q))
        runs = laminar_runs(vals >= threshold)
        means.append(float(np.mean(runs)) if runs else float("nan"))
        counts.append(float(len(runs)))
    alpha, r2 = fit_power(distances, np.asarray(means))
    return {
        "alpha": alpha,
        "r2": r2,
        "means": means,
        "counts": counts,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    kernel = "mean laminar duration follows power-law scaling with distance from the crisis parameter"
    attempts = {
        "phase-laminar-scaling": "mean phase laminar duration follows power law scaling with distance from phase crisis threshold",
        "zero-shadow-laminar-scaling": "zero shadow laminar duration follows power law with distance from zero crisis parameter",
        "finite-prime-burst-scaling": "finite prime burst duration follows cutoff scaling near Euler crisis parameter",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:31s} distance={dist} normalized={dist / max(1, len(kernel)):.4f}")
    print(f"selected={selected}")
    if selected != "phase-laminar-scaling":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #16: use a minimal counterexample")
    print("minimal counterexample: shuffle the same phase-defect values; scaling that survives shuffling is distributional")
    print("kind sigma window alpha r2 shuffled_alpha shuffled_r2 mean_values shuffled_means run_counts")
    primes = first_primes(args.prime_count)
    quantiles = [0.55, 0.62, 0.70, 0.78, 0.86, 0.92]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    for case_index, (sigma, window) in enumerate(cases):
        for kind_index, kind in enumerate(kinds):
            rng = np.random.default_rng(20260621 + 97 * case_index + kind_index)
            vals = profile(kind, sigma, window, args.samples, primes, rng)
            out = scaling(vals, quantiles)
            shuffled = vals.copy()
            rng.shuffle(shuffled)
            sh = scaling(shuffled, quantiles)
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{out['alpha']:.6f} {out['r2']:.6f} {sh['alpha']:.6f} {sh['r2']:.6f} "
                f"{','.join(f'{x:.3f}' for x in out['means'])} "
                f"{','.join(f'{x:.3f}' for x in sh['means'])} "
                f"{','.join(f'{x:.0f}' for x in out['counts'])}"
            )
    print(
        "\nInterpretation key: a non-reducing crisis-scaling signal would need "
        "strong scaling for true that fails under shuffled-value, finite, and "
        "random-phase minimal counterexamples. Otherwise it is threshold/run "
        "statistics or the known phase-defect band."
    )


if __name__ == "__main__":
    main()
