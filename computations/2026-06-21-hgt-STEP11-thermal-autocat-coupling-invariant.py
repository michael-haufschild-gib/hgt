#!/usr/bin/env python3
"""Step 11 invariant test for thermal/autocatalytic HT coupling.

Method #12: Find an invariant.

Candidate invariant:
    timing-coupling excess = coupled max_product minus mean circular-shifted
    heat max_product. Positive true-only excess would suggest genuine
    phase/amplitude timing feedback. Zero or negative excess means the apparent
    runaway is explained by marginal phase and heat loads.
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


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def normalized(x: np.ndarray) -> np.ndarray:
    lo = float(np.quantile(x, 0.05))
    hi = float(np.quantile(x, 0.95))
    if hi <= lo + 1e-12:
        return np.zeros_like(x)
    return np.clip((x - lo) / (hi - lo), 0.0, 1.0)


def traces(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    phase = []
    amp = []
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
        phase.append(d / (1.0 + d))
        amp.append(math.log1p(abs(p)))
    return np.asarray(phase), normalized(np.asarray(amp))


def max_product(phase: np.ndarray, heat_src: np.ndarray) -> float:
    c = 0.03
    heat = 0.0
    best = 0.0
    for p, hsrc in zip(phase, heat_src):
        rate = c * (0.12 + p) * (1.0 + 1.9 * heat)
        c = min(1.0, c + 0.11 * rate)
        heat = max(0.0, 0.82 * heat + 0.28 * hsrc * rate + 0.05 * c - 0.035)
        best = max(best, c * heat)
    return float(best)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=190)
    parser.add_argument("--prime-count", type=int, default=120)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    shifts = [7, 17, 31, 47, 73, 101, 131, 157]
    print("STEP11 method #12 invariant: timing-coupling excess over circular heat shifts")
    print("kind sigma window coupled shift_mean shift_max excess_mean excess_max phase_mean heat_mean")
    for c_i, (sigma, window) in enumerate(cases):
        for k_i, kind in enumerate(kinds):
            phase, heat = traces(kind, sigma, window, args.samples, primes, seed=20260621 + 211 * c_i + k_i)
            coupled = max_product(phase, heat)
            shifted = [max_product(phase, np.roll(heat, shift)) for shift in shifts]
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{coupled:.6f} {np.mean(shifted):.6f} {np.max(shifted):.6f} "
                f"{coupled - np.mean(shifted):.6f} {coupled - np.max(shifted):.6f} "
                f"{np.mean(phase):.6f} {np.mean(heat):.6f}"
            )
    print(
        "\nInterpretation key: positive excess over shifts is required for a "
        "timing-coupled feedback invariant."
    )


if __name__ == "__main__":
    main()
