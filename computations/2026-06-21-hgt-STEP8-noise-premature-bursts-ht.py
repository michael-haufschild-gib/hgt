#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for noise-induced premature bursts.

NODE:
    Noise-induced premature bursts.

Step 8:
    Three attempts are compared by Levenshtein distance.

Step 9 method #10:
    Extreme cases: no added noise, moderate phase noise, high phase noise,
    and extreme thresholds.
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


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
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
        else:
            raise ValueError(kind)
        d = phase_defect(g, p)
        vals.append(d / (1.0 + d))
    return np.asarray(vals)


def premature_metrics(base: np.ndarray, noise: float, threshold: float, seed: int, trials: int = 64) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    base_burst = base >= threshold
    rates = []
    premature_rates = []
    for _ in range(trials):
        noisy = np.clip(base + rng.normal(0.0, noise, size=base.shape), 0.0, 1.0)
        burst = noisy >= threshold
        rates.append(float(np.mean(burst)))
        premature_rates.append(float(np.mean(burst & (~base_burst))))
    return {
        "base_rate": float(np.mean(base_burst)),
        "noisy_rate": float(np.mean(rates)),
        "premature_rate": float(np.mean(premature_rates)),
        "premature_share": float(np.mean(premature_rates) / (np.mean(rates) + 1e-12)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    node = "noise induced premature bursts"
    attempts = {
        "noise-induced-premature-phase-bursts": "noise induced premature phase bursts",
        "zero-shadow-noise-trigger-bursts": "zero shadow noise trigger bursts",
        "prime-jitter-premature-crisis": "prime jitter premature crisis bursts",
    }
    distances = {name: levenshtein(node, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:36s} distance={dist} normalized={dist / len(node):.4f}")
    print(f"selected={selected}")
    if selected != "noise-induced-premature-phase-bursts":
        raise SystemExit("Selected transfer is not implemented in this script.")

    print("\nSTEP9 method #10: extreme cases")
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    thresholds = [0.12, 0.20, 0.32]
    noises = [0.00, 0.03, 0.08, 0.16, 0.28]
    print("kind sigma window threshold noise base_rate noisy_rate premature_rate premature_share")
    for c_i, (sigma, window) in enumerate(cases):
        for k_i, kind in enumerate(kinds):
            base = trace(kind, sigma, window, args.samples, primes, seed=20260621 + 211 * c_i + k_i)
            for threshold in thresholds:
                for noise in noises:
                    out = premature_metrics(base, noise, threshold, seed=303000 + c_i * 1000 + k_i * 100 + int(noise * 1000) + int(threshold * 100))
                    print(
                        f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} {noise:.2f} "
                        f"{out['base_rate']:.6f} {out['noisy_rate']:.6f} {out['premature_rate']:.6f} {out['premature_share']:.6f}"
                    )
    print(
        "\nInterpretation key: a non-reducing result would need premature bursts "
        "to expose a true-specific near-threshold layer that is not just generic "
        "threshold noise applied to phase-defect occupancy."
    )


if __name__ == "__main__":
    main()
