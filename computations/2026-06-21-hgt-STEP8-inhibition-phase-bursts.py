#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for inhibition-organized bursts.

NODE constraint:
    Inhibition can help generate or organize seizures, rather than simply
    suppressing them.

Step 8:
    Create three HT transfer attempts and select the lowest-Levenshtein one.

Step 9 method #21:
    Build a dependency chain:
      inhibition strength -> local suppressive brake -> release/rebound ->
      organized phase-burst run output.
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


def profile(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
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


def moving_average(x: np.ndarray, width: int = 17) -> np.ndarray:
    kernel = np.ones(width) / width
    return np.convolve(x, kernel, mode="same")


def burst_metrics(x: np.ndarray, threshold: float) -> tuple[float, float, float]:
    burst = x > threshold
    runs = []
    cur = 0
    for b in burst:
        if b:
            cur += 1
        elif cur:
            runs.append(cur)
            cur = 0
    if cur:
        runs.append(cur)
    rate = float(np.mean(burst))
    mean_run = float(np.mean(runs)) if runs else 0.0
    return rate, mean_run, float(rate * mean_run)


def inhibited_response(vals: np.ndarray, strength: float) -> dict[str, float]:
    brake = moving_average(vals)
    release = np.maximum(0.0, np.r_[0.0, brake[:-1] - brake[1:]])
    response = np.maximum(0.0, vals - strength * brake + 1.7 * strength * release)
    threshold = float(np.quantile(vals, 0.78))
    rate, run, organized = burst_metrics(response, threshold)
    return {
        "median_response": float(np.median(response)),
        "mean_brake": float(np.mean(strength * brake)),
        "mean_release": float(np.mean(strength * release)),
        "burst_rate": rate,
        "mean_run": run,
        "organized": organized,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=80)
    args = parser.parse_args()

    kernel = "inhibition can help generate or organize seizures rather than simply suppressing them"
    attempts = {
        "inhibition-organized-phase-bursts": "inhibition can help generate or organize phase bursts rather than simply suppressing them",
        "gamma-inhibitory-brake": "gamma inhibitory brake suppresses prime bursts with rebound release",
        "finite-prime-gaba-rebound": "finite prime GABA rebound organizes cutoff seizure bursts",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:35s} distance={dist} normalized={dist / max(1, len(kernel)):.4f}")
    print(f"selected={selected}")
    if selected != "inhibition-organized-phase-bursts":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #21: build a dependency chain")
    print("chain: inhibition_strength -> suppressive_brake + release_rebound -> organized phase-burst runs")
    print("kind sigma window strength median_response mean_brake mean_release burst_rate mean_run organized")
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    strengths = [0.0, 0.25, 0.55, 0.85, 1.20, 1.70]
    for case_index, (sigma, window) in enumerate(cases):
        for kind_index, kind in enumerate(kinds):
            rng = np.random.default_rng(20260621 + 101 * case_index + kind_index)
            vals = profile(kind, sigma, window, args.samples, primes, rng)
            for strength in strengths:
                out = inhibited_response(vals, strength)
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {strength:.2f} "
                    f"{out['median_response']:.6f} {out['mean_brake']:.6f} {out['mean_release']:.6f} "
                    f"{out['burst_rate']:.6f} {out['mean_run']:.6f} {out['organized']:.6f}"
                )
    print(
        "\nInterpretation key: a non-reducing result would need a true-only "
        "nonmonotone organization optimum whose dependency chain fails for finite, "
        "random-phase, amplitude-matched, and right-strip controls."
    )


if __name__ == "__main__":
    main()
