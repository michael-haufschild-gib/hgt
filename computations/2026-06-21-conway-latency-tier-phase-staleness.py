#!/usr/bin/env python3
"""THE-MACHINE run: latency-tier segmentation and phase staleness.

NODE:
    Faster participants may treat stale displayed liquidity differently from
    slower participants, creating stickiness that depends on access speed.

STEP 9 method #19:
    Write the fake proof, then test its gap. Wished proof: the phase-lifetime
    signal is not a stale/coarse-sampling illusion. Gap: observed positive
    phase at a latency tier may not remain positive throughout the latency
    interval.
"""

from __future__ import annotations

import argparse
import math
import runpy
from pathlib import Path

import numpy as np


def load_base():
    remote = Path("/tmp/2026-06-21-conway-kinetic-proofreading-lifetime.py")
    local = Path("computations/2026-06-21-conway-kinetic-proofreading-lifetime.py")
    return runpy.run_path(str(remote if remote.exists() else local))


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    n = 20000
    # Depth episodes are displayed when liquidity appears, then may cancel.
    true_life = rng.geometric(p=0.35, size=n)
    benign_life = rng.geometric(p=0.08, size=n)
    shock = rng.random(n) < 0.25
    life = np.where(shock, true_life, benign_life)
    print("NODE simulation: latency-tier staleness in displayed liquidity")
    print("latency displayed_fill executable_fill stale_positive_frac")
    for latency in [1, 2, 4, 8, 16, 32]:
        displayed = life >= 1
        executable = life >= latency
        stale = displayed & ~executable
        print(
            f"{latency:7d} {float(np.mean(displayed)):.3f} "
            f"{float(np.mean(executable)):.3f} {float(np.mean(stale) / max(np.mean(displayed), 1e-12)):.3f}"
        )


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = cur
    return prev[-1]


def phase_mask(ns, kind: str, sigma: float, window: tuple[float, float], samples: int, primes, rng, threshold: float) -> np.ndarray:
    defects = ns["defects_for"](kind, sigma, window, samples, primes, rng)
    return defects > threshold


def zero_shadow_mask(ns, kind: str, sigma: float, window: tuple[float, float], samples: int, primes, rng, q: float) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = ns["gamma_part"](s)
        if kind == "true":
            p = ns["dlog_zeta"](s)
        elif kind == "finite":
            p = ns["dlog_finite_euler"](s, primes)
        elif kind == "random":
            base = ns["dlog_zeta"](s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(math.log1p(abs(g + p)))
    arr = np.asarray(vals, dtype=float)
    return arr <= float(np.quantile(arr, q))


def latency_metrics(mask: np.ndarray, latency: int) -> dict[str, float]:
    starts = np.arange(0, len(mask) - latency + 1, latency)
    displayed = mask[starts]
    executable = np.array([bool(np.all(mask[i : i + latency])) for i in starts])
    stale = displayed & ~executable
    return {
        "displayed": float(np.mean(displayed)),
        "executable": float(np.mean(executable)),
        "stale_frac": float(np.mean(stale) / max(np.mean(displayed), 1e-12)),
    }


def ht_latency_run(samples: int, prime_count: int, threshold: float) -> None:
    kernel = "displayed liquidity latency executable stale fill access speed"
    attempts = {
        "A_phase_staleness": "displayed phase latency executable persistent stale positive access speed",
        "B_amplitude_staleness": "displayed amplitude latency executable threshold stale magnitude access speed",
        "C_zero_shadow_latency": "displayed zero shadow latency executable stale valley access speed",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:24s} distance={dist}")
    print(f"selected={selected}")

    ns = load_base()
    primes = ns["first_primes"](prime_count)
    rng = np.random.default_rng(721)
    windows = [(100.0, 170.0), (500.0, 570.0), (14.0, 84.0)]
    sigmas = [0.3, 0.5, 1.2]
    latencies = [1, 2, 4, 8, 16, 32]
    print("\nSTEP8/9 HT transfer: selected zero-shadow latency tier")
    print(f"samples={samples} finite_prime_count={prime_count} valley_quantile=0.10")
    print("kind sigma latency displayed executable stale_frac")
    for sigma in sigmas:
        for kind in ["true", "finite", "random"]:
            masks = [zero_shadow_mask(ns, kind, sigma, window, samples, primes, rng, 0.10) for window in windows]
            for latency in latencies:
                rows = [latency_metrics(mask, latency) for mask in masks]
                print(
                    f"{kind:6s} {sigma:.1f} {latency:2d} "
                    f"{float(np.mean([r['displayed'] for r in rows])):.3f} "
                    f"{float(np.mean([r['executable'] for r in rows])):.3f} "
                    f"{float(np.mean([r['stale_frac'] for r in rows])):.3f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=960)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=0.0)
    args = parser.parse_args()
    node_simulation()
    ht_latency_run(args.samples, args.prime_count, args.threshold)


if __name__ == "__main__":
    main()
