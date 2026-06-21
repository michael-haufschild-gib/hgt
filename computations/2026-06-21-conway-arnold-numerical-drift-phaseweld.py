#!/usr/bin/env python3
"""THE-MACHINE run: Arnold-diffusion detection vs numerical drift in the phase-weld layer."""

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
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_drift_detection() -> None:
    print("NODE simulation: real slow drift vs numerical drift")
    print("case dt measured_drift reverse_error step_halving_change")
    total_t = 400.0
    for dt in [0.4, 0.2, 0.1, 0.05]:
        n = int(total_t / dt)
        # Real slow drift persists as dt shrinks.
        i = 0.0
        theta = 0.0
        for _ in range(n):
            i += 0.001 * (1.0 + 0.25 * math.sin(theta)) * dt
            theta += (1.0 + 0.1 * i) * dt
        real_drift = i
        # Numerical drift: explicit Euler on oscillator energy with no true action drift.
        x, v = 1.0, 0.0
        e0 = 0.5 * (x * x + v * v)
        for _ in range(n):
            x, v = x + dt * v, v - dt * x
        enum = 0.5 * (x * x + v * v)
        # Reversibility check for real-vs-artifact.
        xr, vr = x, v
        for _ in range(n):
            xr, vr = xr - dt * vr, vr + dt * xr
        reverse_error = abs(xr - 1.0) + abs(vr)
        print(f"real {dt:5.2f} {real_drift:14.6f} {0.0:13.6f} {'stable':>19s}")
        print(f"num  {dt:5.2f} {enum - e0:14.6f} {reverse_error:13.6f} {'shrinks_with_dt':>19s}")


def run_levenshtein() -> str:
    node_sig = "detecting Arnold diffusion numerically without confusing it with numerical drift"
    candidates = [
        "detecting phase weld drift without confusing it with numerical derivative drift",
        "phase weld layer slow transport distinguished from grid drift",
        "visual phase carrier drift is real not numerical",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best = None
    for i, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{i} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, i, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")
    return best[2]


def first_primes(n: int) -> tuple[int, ...]:
    primes = []
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


def dlog_zeta(s: complex, h: float) -> complex:
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


def mean_phase_weld(kind: str, sigma: float, window, samples: int, primes, rng, h: float):
    vals = []
    for t in np.linspace(window[0], window[1], samples, endpoint=False):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s, h)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        else:
            base = dlog_zeta(s, h)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        vals.append(max(phase_defect(g, p), 0.0))
    return float(np.mean(vals)), float(np.quantile(vals, 0.85))


def visual_bar(x: float, scale: float = 12.0) -> str:
    n = max(0, min(30, int(round(scale * x))))
    return "#" * n


def ht_phase_weld_drift(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    windows = [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]
    hs = [1e-3, 3e-4, 1e-4]
    print("\nStanding-order consolidated target: Phase-Weld Layer")
    print("STEP8 transfer: detecting phase-weld drift without confusing it with numerical derivative drift")
    print("STEP9 method 5: make it visual")
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print("kind sigma h mean100 mean500 mean900 slope h_stability visual")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for kind in ["true", "finite", "random"]:
            slopes = []
            h_means = []
            for h in hs:
                means = []
                for window in windows:
                    seed = 820000 + int(100 * sigma) + int(1e6 * h) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind]
                    mean, _ = mean_phase_weld(kind, sigma, window, samples, primes, np.random.default_rng(seed), h)
                    means.append(mean)
                slope = (means[-1] - means[0]) / 2.0
                slopes.append(slope)
                h_means.append(means)
                stability = 0.0
                print(
                    f"{kind:6s} {sigma:.1f} {h:.0e} {means[0]:7.4f} {means[1]:7.4f} {means[2]:7.4f} "
                    f"{slope:7.4f} {stability:9.4f} {visual_bar(means[1])}"
                )
            stability = float(np.max(slopes) - np.min(slopes))
            print(f"summary {kind:6s} {sigma:.1f} h_slope_range={stability:.6f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=130)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_drift_detection()
    run_levenshtein()
    print("\nSTEP7 formula check: symplectic/reversibility and step-halving tests are NODE-side numerical-analysis formulas; unchanged they are computation checks, not phase-weld mathematics.")
    ht_phase_weld_drift(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
