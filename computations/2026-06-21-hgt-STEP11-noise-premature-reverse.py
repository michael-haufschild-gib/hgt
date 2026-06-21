#!/usr/bin/env python3
"""Step 11 reverse test for noise-induced premature HT bursts.

Method #3: Reverse it.

If premature noisy threshold crossings are meaningful, conditioning on a
premature crossing should reveal a distinctive true analytic near-threshold
layer. If all controls have similar pre-crossing distance-to-threshold and
right-strip collapse, the effect is generic threshold noise.
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


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        true_p = dlog_zeta(s)
        finite_p = dlog_finite_euler(s, primes)
        if kind == "true":
            p = true_p
        elif kind == "finite":
            p = finite_p
        elif kind == "ampmatched-finite":
            p = finite_p * (abs(true_p) / (abs(finite_p) + 1e-300))
        elif kind == "random-phase":
            theta = float(rng.uniform(-math.pi, math.pi))
            p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        d = phase_defect(g, p)
        vals.append(d / (1.0 + d))
    return np.asarray(vals)


def reverse_metrics(base: np.ndarray, threshold: float, noise: float, seed: int, trials: int = 96) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    base_burst = base >= threshold
    distances = []
    indices = []
    for _ in range(trials):
        noisy = np.clip(base + rng.normal(0.0, noise, size=base.shape), 0.0, 1.0)
        premature = (noisy >= threshold) & (~base_burst)
        if np.any(premature):
            distances.extend((threshold - base[premature]).tolist())
            indices.extend(np.where(premature)[0].tolist())
    if distances:
        dist = np.asarray(distances)
        idx = np.asarray(indices)
        return {
            "events": float(len(distances)),
            "distance_med": float(np.median(dist)),
            "distance_q90": float(np.quantile(dist, 0.90)),
            "distance_small_frac": float(np.mean(dist <= noise)),
            "index_entropy": float(len(np.unique(idx)) / len(base)),
        }
    return {"events": 0.0, "distance_med": math.inf, "distance_q90": math.inf, "distance_small_frac": 0.0, "index_entropy": 0.0}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    print("STEP11 method #3 reverse: infer near-threshold layer from premature bursts")
    print("kind sigma window threshold noise events distance_med distance_q90 distance_small_frac index_entropy")
    for c_i, (sigma, window) in enumerate(cases):
        for k_i, kind in enumerate(kinds):
            base = trace(kind, sigma, window, args.samples, primes, seed=20260621 + 211 * c_i + k_i)
            for threshold, noise in [(0.20, 0.08), (0.20, 0.16), (0.32, 0.16)]:
                out = reverse_metrics(base, threshold, noise, seed=909000 + c_i * 100 + k_i * 11 + int(threshold * 1000) + int(noise * 100))
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} {noise:.2f} "
                    f"{out['events']:.0f} {out['distance_med']:.6f} {out['distance_q90']:.6f} "
                    f"{out['distance_small_frac']:.6f} {out['index_entropy']:.6f}"
                )
    print(
        "\nInterpretation key: if finite/random/right-strip controls show the same "
        "small distance-to-threshold conditioning, the reverse claim is generic."
    )


if __name__ == "__main__":
    main()
