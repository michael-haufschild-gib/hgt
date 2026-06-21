#!/usr/bin/env python3
"""Step 11: reverse the coupled-frailty transfer.

Method #3: Reverse it.

Instead of defining visible frailty from multiple low-reserve lanes and asking
whether it occurs, condition on visible failure and ask what explains it. If a
single weakest lane covers almost all visible events, or if independently
shuffled lane timings reproduce the visible-failure fraction, the coupled
reserve metaphor has not produced an independent HT observable.
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


def lane_matrix(kind: str, sigmas: list[float], window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    mat = []
    for sigma in sigmas:
        row = []
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
            row.append(d / (1.0 + d))
        mat.append(row)
    return np.asarray(mat)


def visible_from_low(low: np.ndarray) -> np.ndarray:
    neighbor_low = (np.roll(low, 1, axis=0).astype(float) + np.roll(low, -1, axis=0).astype(float)) / 2.0
    coupled_low = low & (neighbor_low >= 0.5)
    return np.sum(coupled_low, axis=0) >= 3


def reverse_metrics(reserve: np.ndarray, threshold: float, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    low = reserve < threshold
    visible = visible_from_low(low)
    visible_frac = float(np.mean(visible))
    if np.any(visible):
        coverages = [float(np.mean(low[i, visible])) for i in range(low.shape[0])]
        weakest_cover = max(coverages)
    else:
        weakest_cover = 0.0
    weakest_lane_frac = float(np.max(np.mean(low, axis=1)))
    shuffled_fracs = []
    for _ in range(32):
        shuf = low.copy()
        for i in range(shuf.shape[0]):
            rng.shuffle(shuf[i])
        shuffled_fracs.append(float(np.mean(visible_from_low(shuf))))
    return {
        "visible_frac": visible_frac,
        "weakest_lane_frac": weakest_lane_frac,
        "weakest_cover_given_visible": weakest_cover,
        "shuffled_visible_mean": float(np.mean(shuffled_fracs)),
        "shuffled_visible_q90": float(np.quantile(shuffled_fracs, 0.9)),
        "excess_over_shuffle": visible_frac - float(np.mean(shuffled_fracs)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=160)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    boundaries = {
        "left": [0.2, 0.3, 0.4, 0.5, 0.7],
        "middle": [0.5, 0.7, 0.8, 0.9, 1.0],
        "right": [0.9, 1.0, 1.1, 1.2, 1.3],
    }
    windows = [(100.0, 170.0), (500.0, 570.0)]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    print("STEP11 method #3 reverse: explain visible failure from weakest lane / shuffled lanes")
    print("boundary kind window threshold visible_frac weakest_lane_frac weakest_cover_given_visible shuffled_visible_mean shuffled_visible_q90 excess_over_shuffle")
    for b_index, (b_name, sigmas) in enumerate(boundaries.items()):
        for w_index, window in enumerate(windows):
            for k_index, kind in enumerate(kinds):
                reserve = lane_matrix(kind, sigmas, window, args.samples, primes, seed=20260621 + 997 * b_index + 101 * w_index + k_index)
                for threshold in [0.12, 0.20]:
                    out = reverse_metrics(reserve, threshold, seed=404000 + 17 * b_index + 5 * w_index + k_index)
                    print(
                        f"{b_name:7s} {kind:17s} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} "
                        f"{out['visible_frac']:.6f} {out['weakest_lane_frac']:.6f} "
                        f"{out['weakest_cover_given_visible']:.6f} {out['shuffled_visible_mean']:.6f} "
                        f"{out['shuffled_visible_q90']:.6f} {out['excess_over_shuffle']:.6f}"
                    )
    print(
        "\nInterpretation key: a coupled-reserve finding would need visible "
        "failure not covered by one weakest lane and not reproduced by shuffled "
        "lane timings."
    )


if __name__ == "__main__":
    main()
