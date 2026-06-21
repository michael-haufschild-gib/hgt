#!/usr/bin/env python3
"""THE-MACHINE run: sampling misses thin bridges between components."""

from __future__ import annotations

import argparse
import math
from collections import deque

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


def components(mask: np.ndarray):
    h, w = mask.shape
    labels = -np.ones(mask.shape, dtype=int)
    sizes = []
    cid = 0
    for i in range(h):
        for j in range(w):
            if not mask[i, j] or labels[i, j] >= 0:
                continue
            q = deque([(i, j)])
            labels[i, j] = cid
            size = 0
            while q:
                x, y = q.popleft()
                size += 1
                for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < h and 0 <= ny < w and mask[nx, ny] and labels[nx, ny] < 0:
                        labels[nx, ny] = cid
                        q.append((nx, ny))
            sizes.append(size)
            cid += 1
    return labels, sizes


def bridge_stats(mask: np.ndarray) -> dict[str, float]:
    labels, sizes = components(mask)
    total = int(mask.sum())
    if not sizes:
        return {
            "components": 0.0,
            "largest_frac": 0.0,
            "span_sigma": 0.0,
            "span_t": 0.0,
            "thin_cols": 0.0,
            "min_col_width": 0.0,
            "occupied": 0.0,
        }
    largest = int(np.argmax(sizes))
    comp = labels == largest
    col_counts = comp.sum(axis=0)
    row_counts = comp.sum(axis=1)
    positive_cols = col_counts[col_counts > 0]
    span_sigma = bool(np.any(comp[0, :]) and np.any(comp[-1, :]))
    span_t = bool(np.any(comp[:, 0]) and np.any(comp[:, -1]))
    return {
        "components": float(len(sizes)),
        "largest_frac": float(max(sizes) / max(1, total)),
        "span_sigma": float(span_sigma),
        "span_t": float(span_t),
        "thin_cols": float(np.sum((col_counts > 0) & (col_counts <= 2))),
        "min_col_width": float(np.min(positive_cols)) if len(positive_cols) else 0.0,
        "occupied": float(total / mask.size),
    }


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    mask = np.zeros((35, 90), dtype=bool)
    mask[5:25, 5:25] = True
    mask[8:28, 65:85] = True
    mask[15, 25:66] = True
    full = bridge_stats(mask)
    print("NODE simulation: uniform sampling misses a thin bridge and falsely fragments a connected graph")
    print(
        f"full components={full['components']:.0f} largest_frac={full['largest_frac']:.3f} "
        f"span_t={full['span_t']:.0f} thin_cols={full['thin_cols']:.0f}"
    )
    print("sample_p mean_components span_t_rate bridge_recovered_rate")
    bridge = np.zeros_like(mask)
    bridge[15, 25:66] = True
    for p in [0.55, 0.70, 0.85, 0.95]:
        comp_counts = []
        spans = []
        bridge_ok = []
        for _ in range(200):
            sampled = mask & (rng.random(mask.shape) < p)
            st = bridge_stats(sampled)
            comp_counts.append(st["components"])
            spans.append(st["span_t"])
            bridge_ok.append(np.any(sampled & bridge))
        print(f"{p:.2f} {np.mean(comp_counts):.3f} {np.mean(spans):.3f} {np.mean(bridge_ok):.3f}")
    print("strengthened read: high bridge-node detection is not enough; the sampled bridge must remain connected")


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


def zero_shadow_mask(kind: str, sigmas: np.ndarray, ts: np.ndarray, primes: tuple[int, ...], rng: np.random.Generator, threshold: float) -> np.ndarray:
    out = np.zeros((len(sigmas), len(ts)), dtype=bool)
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(ts):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            p = component(kind, s, primes, rng)
            shadow = abs(g + p) / max(abs(g), abs(p), 1e-300)
            out[i, j] = shadow < threshold
    return out


def sampling_stress(mask: np.ndarray, rng: np.random.Generator, p: float, trials: int = 80) -> dict[str, float]:
    full = bridge_stats(mask)
    comps = []
    span_sigma = []
    span_t = []
    largest = []
    for _ in range(trials):
        sampled = mask & (rng.random(mask.shape) < p)
        st = bridge_stats(sampled)
        comps.append(st["components"])
        span_sigma.append(st["span_sigma"])
        span_t.append(st["span_t"])
        largest.append(st["largest_frac"])
    return {
        "full_components": full["components"],
        "full_largest": full["largest_frac"],
        "full_span_sigma": full["span_sigma"],
        "full_span_t": full["span_t"],
        "full_thin_cols": full["thin_cols"],
        "full_min_col_width": full["min_col_width"],
        "occupied": full["occupied"],
        "sample_components": float(np.mean(comps)),
        "sample_span_sigma": float(np.mean(span_sigma)),
        "sample_span_t": float(np.mean(span_t)),
        "sample_largest": float(np.mean(largest)),
    }


def ht_run(samples_t: int, samples_sigma: int, prime_count: int) -> None:
    kernel = "sampling methods miss thin bridges between components"
    attempts = {
        "A_phase_carrier_bridge_graph": "sampling phase carrier misses thin bridges between components",
        "B_zero_shadow_bridge_graph": "sampling zero shadow misses thin bridges between components",
        "C_near_neutral_bridge_graph": "sampling near neutral shell misses thin bridges between components",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:32s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    sigmas = np.linspace(0.2, 0.9, samples_sigma)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    thresholds = [0.50, 0.75, 1.00]
    print("\nSTEP8/9 HT transfer: zero-shadow connectivity bridges")
    print(f"sigma_samples={samples_sigma} t_samples={samples_t} finite_prime_count={prime_count}")
    print("kind window threshold occupied full_comp full_largest span_sigma span_t thin_cols min_col sample_comp sample_span_sigma sample_span_t sample_largest")
    for window in windows:
        ts = np.linspace(window[0], window[1], samples_t)
        for threshold in thresholds:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(550000 + int(window[0]) + int(100 * threshold) + {"true": 1, "finite": 2, "random": 3}[kind])
                mask = zero_shadow_mask(kind, sigmas, ts, primes, rng, threshold)
                st = sampling_stress(mask, rng, p=0.80, trials=80)
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} "
                    f"{st['occupied']:.3f} {st['full_components']:.0f} {st['full_largest']:.3f} "
                    f"{st['full_span_sigma']:.0f} {st['full_span_t']:.0f} {st['full_thin_cols']:.0f} "
                    f"{st['full_min_col_width']:.0f} {st['sample_components']:.2f} "
                    f"{st['sample_span_sigma']:.3f} {st['sample_span_t']:.3f} {st['sample_largest']:.3f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-samples", type=int, default=180)
    parser.add_argument("--sigma-samples", type=int, default=17)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.t_samples, args.sigma_samples, args.prime_count)


if __name__ == "__main__":
    main()
