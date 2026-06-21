#!/usr/bin/env python3
"""THE-MACHINE run: transition-path dynamics vs residence-time statistics."""

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


def node_simulation() -> None:
    rng = np.random.default_rng(20260621)
    dwell_lengths = rng.integers(18, 35, size=16)
    jumpy = []
    smooth = []
    state = 0.0
    for dwell in dwell_lengths:
        next_state = 1.0 - state
        jumpy.extend([next_state] * dwell)
        ramp = np.linspace(state, next_state, 8, endpoint=False).tolist()
        smooth.extend(ramp + [next_state] * max(0, dwell - len(ramp)))
        state = next_state
    jumpy = np.asarray(jumpy)
    smooth = np.asarray(smooth)
    dwell_j = run_lengths(jumpy > 0.5)
    dwell_s = run_lengths(smooth > 0.5)
    edge_j = transition_edges(jumpy, threshold=0.5, band=0.25)
    edge_s = transition_edges(smooth, threshold=0.5, band=0.25)
    print("NODE simulation: same residence scale, different transition paths")
    print(
        f"jumpy median_dwell={np.median(dwell_j):.2f} edge_width={edge_j['edge_width']:.2f} "
        f"edge_slope={edge_j['edge_slope']:.3f}"
    )
    print(
        f"smooth median_dwell={np.median(dwell_s):.2f} edge_width={edge_s['edge_width']:.2f} "
        f"edge_slope={edge_s['edge_slope']:.3f}"
    )


def run_lengths(mask: np.ndarray) -> list[int]:
    out = []
    cur = 0
    for x in mask:
        if bool(x):
            cur += 1
        elif cur:
            out.append(cur)
            cur = 0
    if cur:
        out.append(cur)
    return out


def transition_edges(vals: np.ndarray, threshold: float, band: float) -> dict[str, float]:
    vals = np.asarray(vals, dtype=float)
    mask = vals > threshold
    changes = np.flatnonzero(mask[1:] != mask[:-1]) + 1
    slopes = []
    widths = []
    for idx in changes:
        lo = max(0, idx - 10)
        hi = min(len(vals), idx + 11)
        slopes.append(abs(vals[min(idx, len(vals) - 1)] - vals[max(0, idx - 1)]))
        window = vals[lo:hi]
        widths.append(float(np.sum(np.abs(window - threshold) <= band)))
    runs = run_lengths(mask)
    return {
        "events": float(len(changes)),
        "occupancy": float(np.mean(mask)),
        "median_run": float(np.median(runs)) if runs else 0.0,
        "edge_slope": float(np.median(slopes)) if slopes else 0.0,
        "edge_width": float(np.median(widths)) if widths else 0.0,
        "softness": float((np.median(widths) if widths else 0.0) / max(1e-9, np.median(slopes) if slopes else 0.0)),
    }


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


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


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


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        vals.append(phase_defect(gamma_part(s), component(kind, s, primes, rng)))
    return np.asarray(vals, dtype=float)


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "transition path dynamics differ from residence time statistics"
    attempts = {
        "A_phase_edge_dynamics": "phase transition path dynamics differ from residence time statistics",
        "B_zero_shadow_edge_dynamics": "zero shadow transition path dynamics differ from residence time statistics",
        "C_near_neutral_edge_dynamics": "near neutral transition path dynamics differ from residence time statistics",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:32s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    print("\nSTEP8/9 HT transfer: phase-defect transition-edge dynamics")
    print("kind sigma window events occupancy median_run edge_width edge_slope softness")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for window in windows:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(770000 + int(100 * sigma) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
                vals = trace(kind, sigma, window, samples, primes, rng)
                row = transition_edges(vals, threshold=0.0, band=0.12)
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{row['events']:.0f} {row['occupancy']:.3f} {row['median_run']:.2f} "
                    f"{row['edge_width']:.2f} {row['edge_slope']:.4f} {row['softness']:.2f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=280)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
