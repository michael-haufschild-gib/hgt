#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for reducible partial extinction.

NODE:
    Reducible multi-type systems can have partial extinction distinct from
    global extinction.

Step 8:
    Create three HT attempts and select the lowest Levenshtein transfer.

Step 9 method #13:
    Find a monotone quantity. We vary the survival depth and compare partial
    lane extinction against global sigma-band extinction.
"""

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
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = cur
    return prev[-1]


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
    rows = []
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
        rows.append(row)
    return np.asarray(rows)


def run_lengths(mask: np.ndarray) -> list[int]:
    runs: list[int] = []
    cur = 0
    for b in mask:
        if b:
            cur += 1
        elif cur:
            runs.append(cur)
            cur = 0
    if cur:
        runs.append(cur)
    return runs


def partial_extinction_metrics(reserve: np.ndarray, threshold: float, depth: int) -> dict[str, float]:
    alive = reserve >= threshold
    lane_survive = np.asarray([any(run >= depth for run in run_lengths(row)) for row in alive])
    global_survive = bool(np.any(lane_survive))
    left_component = bool(np.any(lane_survive[:2]))
    right_component = bool(np.any(lane_survive[2:]))
    return {
        "global_survive": float(global_survive),
        "left_survive": float(left_component),
        "right_survive": float(right_component),
        "partial_left_extinct": float((not left_component) and right_component),
        "partial_right_extinct": float(left_component and (not right_component)),
        "surviving_lanes": float(np.sum(lane_survive)),
        "mean_reserve": float(np.mean(reserve)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=170)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    node = "reducible multi type systems partial extinction distinct from global extinction"
    attempts = {
        "reducible-sigma-lane-partial-extinction": "reducible sigma type systems partial extinction distinct from global extinction",
        "multi-type-zero-shadow-extinction-vector": "multi type zero shadow extinction vector not scalar global extinction",
        "prime-cutoff-immigration-survival-split": "prime cutoff immigration survival split across archimedean lanes",
    }
    distances = {name: levenshtein(node, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:42s} distance={dist} normalized={dist / len(node):.4f}")
    print(f"selected={selected}")
    if selected != "reducible-sigma-lane-partial-extinction":
        raise SystemExit("Selected transfer is not implemented in this script.")

    print("\nSTEP9 method #13: monotone survival depth")
    primes = first_primes(args.prime_count)
    cases = {
        "left_band": [0.2, 0.3, 0.5, 0.7],
        "middle_band": [0.5, 0.7, 0.9, 1.0],
        "right_band": [0.9, 1.0, 1.2, 1.3],
    }
    windows = [(100.0, 170.0), (500.0, 570.0)]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    depths = [4, 8, 12, 18, 26, 36]
    threshold = 0.20
    print("band kind window depth global_survive left_survive right_survive partial_left_extinct partial_right_extinct surviving_lanes mean_reserve")
    for b_i, (band, sigmas) in enumerate(cases.items()):
        for w_i, window in enumerate(windows):
            for k_i, kind in enumerate(kinds):
                reserve = lane_matrix(kind, sigmas, window, args.samples, primes, seed=20260621 + 1000 * b_i + 101 * w_i + k_i)
                for depth in depths:
                    out = partial_extinction_metrics(reserve, threshold, depth)
                    print(
                        f"{band:11s} {kind:17s} [{window[0]:.0f},{window[1]:.0f}] {depth:2d} "
                        f"{out['global_survive']:.0f} {out['left_survive']:.0f} {out['right_survive']:.0f} "
                        f"{out['partial_left_extinct']:.0f} {out['partial_right_extinct']:.0f} "
                        f"{out['surviving_lanes']:.0f} {out['mean_reserve']:.6f}"
                    )
    print(
        "\nInterpretation key: a non-reducing result would need partial lane "
        "extinction to reveal vector survival not already captured by existing "
        "single-lane phase-run persistence."
    )


if __name__ == "__main__":
    main()
