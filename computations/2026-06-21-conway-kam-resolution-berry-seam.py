#!/usr/bin/env python3
"""THE-MACHINE run: finite-resolution KAM false tori and Berry seam equalization."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


ZEROS = [14.134725141734693, 21.022039638771554, 25.01085758014569, 30.424876125859513, 32.93506158773919]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_resolution_false_tori() -> None:
    print("NODE simulation: finite resolution mistakes sticky chaotic layers for intact tori")
    print("jump_rate samples rotation_var jumps_seen classified_regular")
    rng = np.random.default_rng(310209)
    total = 24000
    for jump_rate in [0.0005, 0.0020, 0.0080]:
        increments = 0.381966 + rng.normal(0.0, 0.0008, size=total)
        jump_mask = rng.random(total) < jump_rate
        increments[jump_mask] += rng.choice([-0.19, 0.23], size=int(np.sum(jump_mask)))
        y = np.cumsum(increments) % 1.0
        for samples in [32, 128, 512, 2048]:
            idx = np.linspace(0, len(y) - 1, samples, dtype=int)
            sampled_steps = np.diff(np.unwrap(2.0 * math.pi * y[idx])) / max(total / samples, 1.0)
            rot_var = float(np.var(sampled_steps))
            jumps_seen = int(np.sum(jump_mask[idx]))
            regular = int(rot_var < 0.00035)
            print(f"{jump_rate:9.4f} {samples:5d} {rot_var:12.6f} {jumps_seen:10d} {regular:d}")


def run_levenshtein() -> str:
    node_sig = "finite numerical resolution can mistake sticky chaotic layers for intact tori"
    candidates = [
        "finite resolution can mistake berry seam layers for intact equalization",
        "low resolution can mistake berry lane imbalance for seam equalization",
        "sampling resolution can hide two path berry seam breakup",
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


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def field_value(kind: str, s: complex, primes, rng) -> complex:
    p = dlog_zeta(s)
    if kind == "bare":
        return p
    if kind == "xi":
        return gamma_part(s) + p
    if kind == "finite_xi":
        return gamma_part(s) + dlog_finite_euler(s, primes)
    if kind == "random_xi":
        theta = rng.uniform(-math.pi, math.pi)
        return gamma_part(s) + abs(p) * complex(math.cos(theta), math.sin(theta))
    raise ValueError(kind)


def lane_amplitude(kind: str, center_sigma: float, zero_t: float, delta: float, samples: int, primes, rng):
    left_sigma = center_sigma - delta
    right_sigma = center_sigma + delta
    width = 0.55
    ts = np.linspace(zero_t - width, zero_t + width, samples)
    weight = np.exp(-((ts - zero_t) / (0.42 * width + 1e-12)) ** 2)
    left = 0.0 + 0.0j
    right = 0.0 + 0.0j
    for t, w in zip(ts, weight):
        left += w * field_value(kind, complex(left_sigma, float(t)), primes, rng)
        right += w * field_value(kind, complex(right_sigma, float(t)), primes, rng)
    left /= float(np.sum(weight))
    right /= float(np.sum(weight))
    imbalance = abs(abs(left) - abs(right)) / (abs(left) + abs(right) + 1e-12)
    rel_phase = abs(math.atan2((left / (right + 1e-300)).imag, (left / (right + 1e-300)).real))
    return float(imbalance), float(rel_phase)


def ht_berry_resolution(samples_list, prime_count: int) -> None:
    primes = first_primes(prime_count)
    print("\nStanding-order consolidated target: Berry Seam Layer")
    print("STEP8 transfer: finite resolution can mistake Berry seam layers for intact equalization")
    print("STEP9 method 15: strengthen the test")
    print("Strengthened gate: seam equalization must be resolution-stable, off-seam broken, and not reproduced by finite/random controls.")
    print(f"prime_count={prime_count}")
    print("kind center samples mean_imbalance max_imbalance mean_phase false_equalized")
    for center in [0.5, 0.58]:
        for kind in ["bare", "xi", "finite_xi", "random_xi"]:
            for samples in samples_list:
                imbs = []
                phases = []
                for z in ZEROS:
                    seed = 914000 + int(1000 * center) + samples + int(10 * z) + {"bare": 1, "xi": 2, "finite_xi": 3, "random_xi": 4}[kind]
                    imb, phase = lane_amplitude(kind, center, z, 0.16, samples, primes, np.random.default_rng(seed))
                    imbs.append(imb)
                    phases.append(phase)
                mean_imb = float(np.mean(imbs))
                max_imb = float(np.max(imbs))
                mean_phase = float(np.mean(phases))
                false_equalized = int(mean_imb < 0.08 and center != 0.5)
                print(f"{kind:9s} {center:.2f} {samples:5d} {mean_imb:14.6f} {max_imb:13.6f} {mean_phase:10.6f} {false_equalized:d}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--samples", type=str, default="24,48,96,192")
    args = parser.parse_args()
    samples_list = [int(x) for x in args.samples.split(",") if x.strip()]
    node_resolution_false_tori()
    run_levenshtein()
    print("\nSTEP7 formula check: Greene/KAM residue and resolution tests are NODE-side diagnostics. Unchanged use would be generic numerical classification, not Berry seam geometry.")
    ht_berry_resolution(samples_list, args.prime_count)


if __name__ == "__main__":
    main()
