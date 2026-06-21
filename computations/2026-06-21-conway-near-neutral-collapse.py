#!/usr/bin/env python3
"""THE-MACHINE run: near-neutral measurement collapse.

NODE:
    Experimental fitness measurements often collapse near-neutral differences
    that matter over evolutionary time.

Constraint:
    A finite measurement resolution maps small selection coefficients to
    "neutral", while the same coefficients compound under repeated
    reproduction.

STEP 9 method #1:
    Split into subclaims:
      (i) the per-step differences are below measurement resolution;
      (ii) the collapsed differences have a biased sign or mean;
      (iii) iteration turns the hidden bias into a large cumulative effect.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

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


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    true_s = np.asarray([0.0, 0.0008, -0.0007, 0.0011])
    noise_sd = 0.006
    reps = 10
    measurements = true_s[:, None] + noise_sd * rng.normal(size=(len(true_s), reps))
    means = measurements.mean(axis=1)
    se = measurements.std(axis=1, ddof=1) / math.sqrt(reps)
    measured_neutral = np.abs(means) < 2.0 * se

    freqs = np.full(len(true_s), 1.0 / len(true_s))
    print("NODE simulation: finite fitness resolution hides compounding near-neutral selection")
    print("genotype true_s measured_mean two_se measured_neutral freq_T1000 freq_T5000")
    freqs_1000 = None
    for gen in range(1, 5001):
        freqs = freqs * np.exp(true_s)
        freqs = freqs / np.sum(freqs)
        if gen == 1000:
            freqs_1000 = freqs.copy()
    assert freqs_1000 is not None
    for i, s in enumerate(true_s):
        print(
            f"{i:8d} {s:+.6f} {means[i]:+.6f} {2.0 * se[i]:.6f} "
            f"{int(measured_neutral[i])} {freqs_1000[i]:.4f} {freqs[i]:.4f}"
        )
    ratio = math.exp((true_s[3] - true_s[0]) * 5000)
    print(f"subclaim_iii best_vs_neutral_ratio_T5000={ratio:.3f}")


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


def component(kind: str, s: complex, primes: tuple[int, ...], rng: np.random.Generator) -> complex:
    if kind == "true":
        return dlog_zeta(s)
    if kind == "finite":
        return dlog_finite_euler(s, primes)
    if kind == "random":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        return abs(base) * complex(math.cos(theta), math.sin(theta))
    raise ValueError(kind)


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        vals.append(phase_defect(gamma_part(s), component(kind, s, primes, rng)))
    return np.asarray(vals, dtype=float)


@dataclass(frozen=True)
class HiddenRow:
    hidden_frac: float
    hidden_mean: float
    hidden_sum: float
    hidden_pos_frac: float
    visible_mean: float
    total_mean: float
    exp_hidden: float


def hidden_advantage_row(advantage: np.ndarray, epsilon: float) -> HiddenRow:
    hidden = np.abs(advantage) <= epsilon
    visible = ~hidden
    if np.any(hidden):
        hidden_vals = advantage[hidden]
        hidden_mean = float(np.mean(hidden_vals))
        hidden_sum = float(np.sum(hidden_vals))
        hidden_pos_frac = float(np.mean(hidden_vals > 0.0))
    else:
        hidden_mean = 0.0
        hidden_sum = 0.0
        hidden_pos_frac = 0.0
    visible_mean = float(np.mean(advantage[visible])) if np.any(visible) else 0.0
    # Report a bounded compounding factor for the hidden mean over 100 neutral steps.
    exp_hidden = float(math.exp(max(-50.0, min(50.0, 100.0 * hidden_mean))))
    return HiddenRow(
        hidden_frac=float(np.mean(hidden)),
        hidden_mean=hidden_mean,
        hidden_sum=hidden_sum,
        hidden_pos_frac=hidden_pos_frac,
        visible_mean=visible_mean,
        total_mean=float(np.mean(advantage)),
        exp_hidden=exp_hidden,
    )


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "near neutral fitness measurement collapse cumulative evolutionary advantage"
    attempts = {
        "A_phase_microadvantage_accumulation": "near neutral phase measurement collapse cumulative t advantage",
        "B_sigma_lane_microdrift": "near neutral sigma lane measurement collapse cumulative strip advantage",
        "C_zero_shadow_microselection": "near neutral zero shadow measurement collapse cumulative valley advantage",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:36s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    sigmas = [0.2, 0.3, 0.5, 0.7, 0.9, 1.2]
    epsilons = [0.05, 0.10, 0.20]
    print("\nSTEP8/9 HT transfer: locally collapsed phase advantage")
    print(f"samples={samples} finite_prime_count={prime_count}")
    print("control sigma window eps hidden_frac hidden_mean hidden_sum hidden_pos visible_mean total_mean exp100_hidden")
    for sigma in sigmas:
        for window in windows:
            true_vals = trace("true", sigma, window, samples, primes, np.random.default_rng(101))
            for control in ["finite", "random"]:
                rng = np.random.default_rng(444000 + int(100 * sigma) + int(window[0]) + {"finite": 2, "random": 3}[control])
                control_vals = trace(control, sigma, window, samples, primes, rng)
                advantage = true_vals - control_vals
                for eps in epsilons:
                    row = hidden_advantage_row(advantage, eps)
                    print(
                        f"{control:7s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {eps:.2f} "
                        f"{row.hidden_frac:.3f} {row.hidden_mean:+.5f} {row.hidden_sum:+.5f} "
                        f"{row.hidden_pos_frac:.3f} {row.visible_mean:+.5f} {row.total_mean:+.5f} "
                        f"{row.exp_hidden:.3f}"
                    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
