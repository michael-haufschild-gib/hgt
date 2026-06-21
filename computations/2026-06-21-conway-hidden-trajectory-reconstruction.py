#!/usr/bin/env python3
"""THE-MACHINE run: inferred work/heat vs hidden trajectory reconstruction."""

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


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    observed = rng.normal(0, 1, size=300).cumsum()
    hidden_a = np.sign(np.gradient(observed))
    hidden_b = hidden_a.copy()
    flip = rng.random(len(hidden_b)) < 0.22
    hidden_b[flip] *= -1
    work = float(observed[-1] - observed[0])
    heat_a = float(np.sum(np.abs(np.diff(hidden_a))))
    heat_b = float(np.sum(np.abs(np.diff(hidden_b))))
    print("NODE simulation: same observed work can hide different reconstructed heat")
    print(f"observed_work={work:+.6f} heat_model_A={heat_a:.1f} heat_model_B={heat_b:.1f} hidden_flip_rate={np.mean(flip):.3f}")


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
    phase = []
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
        phase.append(math.atan2((g * p.conjugate()).imag, (g * p.conjugate()).real))
        defect.append(phase_defect(g, p))
    return np.asarray(amp), np.unwrap(np.asarray(phase)), np.asarray(defect)


def hidden_metrics(amp: np.ndarray, phase: np.ndarray, defect: np.ndarray) -> dict[str, float]:
    amp_work = float(amp[-1] - amp[0])
    amp_variation = float(np.sum(np.abs(np.diff(amp))))
    phase_heat = float(np.sum(np.abs(np.diff(phase))))
    defect_heat = float(np.sum(np.abs(np.diff(defect))))
    return {
        "amp_work": amp_work,
        "amp_variation": amp_variation,
        "phase_heat": phase_heat,
        "defect_heat": defect_heat,
        "hidden_ratio": phase_heat / max(1e-9, amp_variation),
        "median_defect": float(np.median(defect)),
    }


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "inferred work heat model dependent hidden stochastic trajectories"
    attempts = {
        "A_amplitude_work_hidden_phase_heat": "inferred amplitude work model dependent hidden phase trajectories",
        "B_zero_shadow_work_hidden_path": "inferred zero shadow work model dependent hidden path trajectories",
        "C_sigma_lane_work_hidden_switches": "inferred sigma lane work model dependent hidden switch trajectories",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:38s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    windows = [(100.0, 170.0), (500.0, 570.0)]
    print("\nSTEP8/9 HT transfer: observed amplitude work vs hidden phase heat")
    print("kind sigma window amp_work amp_var phase_heat defect_heat hidden_ratio median_defect")
    for sigma in [0.3, 0.5, 1.2]:
        for window in windows:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(990000 + int(100 * sigma) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
                row = hidden_metrics(*trace(kind, sigma, window, samples, primes, rng))
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{row['amp_work']:+.4f} {row['amp_variation']:.4f} {row['phase_heat']:.4f} "
                    f"{row['defect_heat']:.4f} {row['hidden_ratio']:.3f} {row['median_defect']:.4f}"
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
