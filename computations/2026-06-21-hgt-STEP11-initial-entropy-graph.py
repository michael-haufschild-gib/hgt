#!/usr/bin/env python3
"""THE-MACHINE Step 11: change representation for phase association.

Represent sigma-lane event association as a graph/correlation matrix rather
than as a scalar empirical-density variance. This attacks marginal-occupancy
confounds in the initial-measure entropy-gate candidate.
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


def fields(sigmas: list[float], window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> dict[str, np.ndarray]:
    out = {kind: np.zeros((samples, len(sigmas)), dtype=float) for kind in ["true", "finite", "random"]}
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            fp = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            out["true"][j, i] = phase_defect(g, zp)
            out["finite"][j, i] = phase_defect(g, fp)
            out["random"][j, i] = phase_defect(g, rp)
    return out


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


def graph_metrics(events: np.ndarray) -> dict[str, float]:
    x = events.astype(float)
    p = np.mean(x, axis=0)
    centered = x - p[None, :]
    cov = centered.T @ centered / x.shape[0]
    sd = np.sqrt(np.diag(cov) + 1e-12)
    corr = cov / (sd[:, None] * sd[None, :])
    np.fill_diagonal(corr, 0.0)
    np.fill_diagonal(cov, 0.0)
    off = corr[~np.eye(corr.shape[0], dtype=bool)]
    eig = np.linalg.eigvalsh(corr)
    adj20 = corr > 0.20
    adj35 = corr > 0.35
    return {
        "occ": float(np.mean(x)),
        "corr_mean": float(np.mean(off)),
        "corr_abs": float(np.mean(np.abs(off))),
        "corr_top_eig": float(eig[-1]),
        "edges20": float(np.count_nonzero(np.triu(adj20, 1))),
        "edges35": float(np.count_nonzero(np.triu(adj35, 1))),
        "comp20": float(largest_component(adj20)),
        "comp35": float(largest_component(adj35)),
        "marginal_min": float(np.min(p)),
        "marginal_max": float(np.max(p)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=640)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211717)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    primes = first_primes(args.prime_count)
    print("STEP11 phase association graph representation")
    print(f"samples={args.samples} prime_count={args.prime_count} method=17 change_representation")
    print("kind window threshold_mode occ corr_mean corr_abs corr_top_eig edges20 edges35 comp20 comp35 marginal_min marginal_max")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        data = fields(sigmas, window, args.samples, primes, rng)
        thresholds = {
            "true_q70": float(np.quantile(data["true"], 0.70)),
            "true_q85": float(np.quantile(data["true"], 0.85)),
        }
        for mode, threshold in thresholds.items():
            for kind in ["true", "finite", "random"]:
                row = graph_metrics(data[kind] > threshold)
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {mode:8s} "
                    f"{row['occ']:.4f} {row['corr_mean']:.4f} {row['corr_abs']:.4f} "
                    f"{row['corr_top_eig']:.4f} {row['edges20']:.0f} {row['edges35']:.0f} "
                    f"{row['comp20']:.0f} {row['comp35']:.0f} "
                    f"{row['marginal_min']:.4f} {row['marginal_max']:.4f}"
                )
    print("\nreduction gate")
    print("Promote only if true has a stronger normalized association graph than finite/random without degenerate marginals.")


if __name__ == "__main__":
    main()
