#!/usr/bin/env python3
"""STEP 12 battery: phase initial-measure association gate.

Meaningful scientific-method coverage:
    1 split subclaims: association excess, graph eigenvalue, edge connectivity.
    2 attack false: finite-prime and random-phase controls.
    10 test extremes: q60/q70/q85 thresholds.
    12 invariant: normalized correlation graph, not raw covariance only.
    13 monotone: cutoff stress across N.
    22 nearby false statement: independently shuffle lanes, preserving marginals.
    23 boundary cases: low/high windows and marginal degeneracy.
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


def dlog_finite(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def build_fields(
    sigmas: list[float],
    window: tuple[float, float],
    samples: int,
    prime_sets: dict[int, tuple[int, ...]],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    fields: dict[str, np.ndarray] = {
        "true": np.zeros((samples, len(sigmas)), dtype=float),
        "random": np.zeros((samples, len(sigmas)), dtype=float),
    }
    for n in prime_sets:
        fields[f"finite{n}"] = np.zeros((samples, len(sigmas)), dtype=float)
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            fields["true"][j, i] = phase_defect(g, zp)
            fields["random"][j, i] = phase_defect(g, rp)
            for n, primes in prime_sets.items():
                fields[f"finite{n}"][j, i] = phase_defect(g, dlog_finite(s, primes))
    return fields


def largest_component(adj: np.ndarray) -> int:
    n = adj.shape[0]
    seen = set()
    best = 0
    for start in range(n):
        if start in seen:
            continue
        stack = [start]
        seen.add(start)
        size = 0
        while stack:
            v = stack.pop()
            size += 1
            for w in np.flatnonzero(adj[v]):
                if int(w) not in seen:
                    seen.add(int(w))
                    stack.append(int(w))
        best = max(best, size)
    return best


def metrics(events: np.ndarray) -> dict[str, float]:
    x = events.astype(float)
    p = np.mean(x, axis=0)
    lane_count = x.shape[1]
    empirical_mean = np.mean(x, axis=1)
    joint_var = float(np.var(empirical_mean))
    product_var = float(np.sum(p * (1.0 - p)) / (lane_count * lane_count))
    centered = x - p[None, :]
    cov = centered.T @ centered / x.shape[0]
    sd = np.sqrt(np.diag(cov) + 1e-12)
    corr = cov / (sd[:, None] * sd[None, :])
    np.fill_diagonal(corr, 0.0)
    off = corr[~np.eye(lane_count, dtype=bool)]
    eig = np.linalg.eigvalsh(corr)
    adj20 = corr > 0.20
    return {
        "occ": float(np.mean(x)),
        "assoc_excess": joint_var - product_var,
        "excess_ratio": float((joint_var - product_var) / max(product_var, 1e-12)),
        "corr_mean": float(np.mean(off)),
        "corr_top_eig": float(eig[-1]),
        "edges20": float(np.count_nonzero(np.triu(adj20, 1))),
        "comp20": float(largest_component(adj20)),
        "marginal_min": float(np.min(p)),
        "marginal_max": float(np.max(p)),
    }


def lane_shuffle(events: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    out = events.copy()
    for i in range(out.shape[1]):
        rng.shuffle(out[:, i])
    return out


def shuffled_eig(events: np.ndarray, rng: np.random.Generator, reps: int = 8) -> float:
    return float(np.mean([metrics(lane_shuffle(events, rng))["corr_top_eig"] for _ in range(reps)]))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=480)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211217)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    finite_counts = [30, 80, 160, 240, 400]
    prime_sets = {n: first_primes(n) for n in finite_counts}
    windows = [(14.0, 84.0), (100.0, 170.0), (260.0, 330.0), (500.0, 570.0)]
    qs = [0.60, 0.70, 0.85]
    print("STEP12 phase initial-measure association battery")
    print(f"samples={args.samples} finite_counts={finite_counts} thresholds={qs}")
    print("window q true_eig true_edges true_assoc true_shuffle_eig max_finite_eig random_eig eig_gap survives finite_eigs")
    survival = 0
    trials = 0
    for window in windows:
        fields = build_fields(sigmas, window, args.samples, prime_sets, rng)
        for q in qs:
            threshold = float(np.quantile(fields["true"], q))
            true_events = fields["true"] > threshold
            true = metrics(true_events)
            shuf = shuffled_eig(true_events, rng)
            finite_eigs = []
            for n in finite_counts:
                finite_eigs.append(metrics(fields[f"finite{n}"] > threshold)["corr_top_eig"])
            random_eig = metrics(fields["random"] > threshold)["corr_top_eig"]
            max_finite = max(finite_eigs)
            gap = true["corr_top_eig"] - max(max_finite, random_eig)
            nondegenerate = true["marginal_max"] < 0.97 and true["marginal_min"] > 0.0
            ok = gap > 0.90 and true["edges20"] >= 14 and true["corr_top_eig"] > 2.4 and shuf < 0.45 and nondegenerate
            survival += int(ok)
            trials += 1
            print(
                f"[{window[0]:.0f},{window[1]:.0f}] {q:.2f} "
                f"{true['corr_top_eig']:.4f} {true['edges20']:.0f} {true['assoc_excess']:.5f} "
                f"{shuf:.4f} {max_finite:.4f} {random_eig:.4f} {gap:.4f} {int(ok)} "
                + ",".join(f"N{n}:{eig:.3f}" for n, eig in zip(finite_counts, finite_eigs))
            )
    print(f"\nSURVIVAL_THRESHOLDS {survival}/{trials}")
    print("interpretation: robust if most q70/q85 left/mid/high windows survive finite-cutoff and lane-shuffle attacks; q60 is a lower-threshold stress case.")


if __name__ == "__main__":
    main()
