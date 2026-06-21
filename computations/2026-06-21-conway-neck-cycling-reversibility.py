#!/usr/bin/env python3
"""THE-MACHINE run: neck opening/closure reversibility under cycling."""

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
    pressures = np.r_[np.linspace(0, 1, 80), np.linspace(1, 0, 80)]
    reversible = pressures > 0.50
    hysteretic = []
    state = False
    for p in pressures:
        if p > 0.62:
            state = True
        if p < 0.38:
            state = False
        hysteretic.append(state)
    hysteretic = np.asarray(hysteretic, dtype=bool)
    up = slice(0, 80)
    down = slice(80, 160)
    rev_area = float(abs(np.mean(reversible[up]) - np.mean(reversible[down])))
    hys_area = float(abs(np.mean(hysteretic[up]) - np.mean(hysteretic[down])))
    print("NODE simulation: neck cycling distinguishes reversible thresholding from hysteresis")
    print(f"reversible_loop_area={rev_area:.3f} hysteretic_loop_area={hys_area:.3f}")
    print("visual reversible:")
    print("".join("#" if x else "." for x in reversible[::4]))
    print("visual hysteretic:")
    print("".join("#" if x else "." for x in hysteretic[::4]))


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


def zero_shadow_values(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p = component(kind, s, primes, rng)
        vals.append(abs(g + p) / max(abs(g), abs(p), 1e-300))
    return np.asarray(vals, dtype=float)


def loop_metrics(vals: np.ndarray, thresholds: np.ndarray, memory_gap: float) -> tuple[float, float, str, str]:
    up_fracs = []
    down_fracs = []
    up_visual = []
    down_visual = []
    state = np.zeros_like(vals, dtype=bool)
    for th in thresholds:
        open_now = vals < th
        if memory_gap <= 0:
            state = open_now
        else:
            state = open_now | (state & (vals < th + memory_gap))
        up_fracs.append(float(np.mean(state)))
        up_visual.append("#" if np.mean(state) > 0.5 else ".")
    for th in thresholds[::-1]:
        open_now = vals < th
        if memory_gap <= 0:
            state = open_now
        else:
            state = open_now | (state & (vals < th + memory_gap))
        down_fracs.append(float(np.mean(state)))
        down_visual.append("#" if np.mean(state) > 0.5 else ".")
    loop_area = float(np.mean(np.abs(np.asarray(up_fracs) - np.asarray(down_fracs[::-1]))))
    final_offset = float(down_fracs[-1] - up_fracs[0])
    return loop_area, final_offset, "".join(up_visual), "".join(down_visual)


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "neck closure opening reversible under cycling conditions"
    attempts = {
        "A_zero_shadow_neck_cycling": "zero shadow closure opening reversible under cycling conditions",
        "B_phase_bridge_cycle": "phase bridge closure opening reversible under cycling conditions",
        "C_prime_cutoff_hysteresis": "prime cutoff closure opening reversible under cycling conditions",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:28s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    thresholds = np.linspace(0.45, 1.15, 12)
    windows = [(100.0, 170.0), (500.0, 570.0)]
    print("\nSTEP8/9 HT transfer: zero-shadow neck cycling visualization")
    print("kind sigma window memory_gap loop_area final_offset up_visual down_visual")
    for sigma in [0.3, 0.7, 1.2]:
        for window in windows:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(660000 + int(100 * sigma) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
                vals = zero_shadow_values(kind, sigma, window, samples, primes, rng)
                for gap in [0.0, 0.12]:
                    loop_area, final_offset, up_vis, down_vis = loop_metrics(vals, thresholds, gap)
                    print(
                        f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {gap:.2f} "
                        f"{loop_area:.4f} {final_offset:+.4f} {up_vis} {down_vis}"
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
