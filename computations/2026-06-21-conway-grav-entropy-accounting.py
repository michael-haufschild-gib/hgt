#!/usr/bin/env python3
"""THE-MACHINE run: matter entropy vs gravitational/structure entropy accounting."""

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


def entropy(probs: np.ndarray) -> float:
    probs = probs[probs > 0]
    return float(-np.sum(probs * np.log(probs)))


def hist_entropy(vals: np.ndarray, bins: int = 12) -> float:
    counts, _ = np.histogram(vals, bins=bins)
    return entropy(counts / max(1, np.sum(counts)))


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


def node_simulation() -> None:
    uniform = np.ones(1000)
    clumped = np.r_[np.ones(80) * 12.5, np.zeros(920)]
    matter_uniform = hist_entropy(uniform + np.linspace(0, 1e-6, len(uniform)))
    matter_clumped = hist_entropy(clumped)
    grav_uniform = float(np.var(uniform) / (np.mean(uniform) ** 2 + 1e-9))
    grav_clumped = float(np.var(clumped) / (np.mean(clumped) ** 2 + 1e-9))
    print("NODE simulation: ordinary density entropy and gravitational clumping entropy disagree")
    print(f"uniform matter_entropy={matter_uniform:.4f} gravitational_clumping={grav_uniform:.4f}")
    print(f"clumped matter_entropy={matter_clumped:.4f} gravitational_clumping={grav_clumped:.4f}")


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


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator):
    amp = []
    defect = []
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
        amp.append(math.log1p(abs(p)))
        defect.append(phase_defect(g, p))
    return np.asarray(amp), np.asarray(defect)


def structure_entropy(defect: np.ndarray, threshold: float = 0.0) -> float:
    runs = np.asarray(run_lengths(defect > threshold), dtype=float)
    if len(runs) == 0:
        return 0.0
    return entropy(runs / np.sum(runs))


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "low entropy early universe not small hot dense gravitational accounting"
    attempts = {
        "A_phase_clumping_entropy": "low phase entropy not small amplitude dense structure accounting",
        "B_zero_shadow_topology_entropy": "low zero shadow entropy not small amplitude dense topology accounting",
        "C_sigma_lane_record_entropy": "low sigma lane entropy not small amplitude dense record accounting",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:34s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    windows = [(100.0, 170.0), (500.0, 570.0)]
    print("\nSTEP8/9 HT transfer: amplitude entropy vs phase-structure entropy")
    print("kind window sigma amp_entropy structure_entropy median_defect run_count")
    for window in windows:
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(123000 + int(100 * sigma) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
                amp, defect = trace(kind, sigma, window, samples, primes, rng)
                runs = run_lengths(defect > 0)
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {sigma:.1f} "
                    f"{hist_entropy(amp):.4f} {structure_entropy(defect):.4f} "
                    f"{float(np.median(defect)):.4f} {len(runs)}"
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
