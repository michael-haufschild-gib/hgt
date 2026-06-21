#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for coupled reserve frailty.

NODE:
    Frailty can be understood as a visible failure of reserve across multiple
    coupled systems.

Step 8:
    Three HT attempts are compared by Levenshtein distance.

Step 9 method #23:
    Classify boundary cases for coupled phase-reserve failure.
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


def coupled_frailty_metrics(reserve: np.ndarray, threshold: float, coupling: float) -> dict[str, float]:
    low = reserve < threshold
    neighbor_low = (np.roll(low, 1, axis=0).astype(float) + np.roll(low, -1, axis=0).astype(float)) / 2.0
    coupled_low = low & (neighbor_low >= coupling)
    visible = np.sum(coupled_low, axis=0) >= 3
    mean_reserve = float(np.mean(reserve))
    min_lane_median = float(np.min(np.median(reserve, axis=1)))
    return {
        "mean_reserve": mean_reserve,
        "min_lane_median": min_lane_median,
        "visible_frac": float(np.mean(visible)),
        "peak_failed_lanes": float(np.max(np.sum(coupled_low, axis=0))),
        "all_lane_failure_frac": float(np.mean(np.all(low, axis=0))),
        "resting_ok_frac": float(np.mean(np.mean(reserve, axis=0) >= threshold)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=160)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    node = "frailty visible failure reserve across multiple coupled systems"
    attempts = {
        "frailty-visible-phase-reserve-across-coupled-sigma-systems": "frailty visible failure of phase reserve across multiple coupled sigma systems",
        "coupled-zero-shadow-reserve-cascade": "coupled zero shadow reserve cascade across strip lanes",
        "archimedean-prime-organ-failure-index": "archimedean prime organ failure index under reserve loss",
    }
    distances = {name: levenshtein(node, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:58s} distance={dist} normalized={dist / len(node):.4f}")
    print(f"selected={selected}")
    if selected != "frailty-visible-phase-reserve-across-coupled-sigma-systems":
        raise SystemExit("Selected transfer is not implemented in this script.")

    print("\nSTEP9 method #23: classify boundary cases")
    primes = first_primes(args.prime_count)
    windows = [(100.0, 170.0), (500.0, 570.0)]
    boundaries = {
        "left": [0.2, 0.3, 0.4, 0.5, 0.7],
        "middle": [0.5, 0.7, 0.8, 0.9, 1.0],
        "right": [0.9, 1.0, 1.1, 1.2, 1.3],
    }
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    print("boundary kind window threshold coupling mean_reserve min_lane_median resting_ok_frac visible_frac peak_failed_lanes all_lane_failure_frac")
    for boundary_name, sigmas in boundaries.items():
        for window_index, window in enumerate(windows):
            for kind_index, kind in enumerate(kinds):
                reserve = lane_matrix(kind, sigmas, window, args.samples, primes, seed=20260621 + 1000 * window_index + 31 * kind_index)
                for threshold in [0.12, 0.20, 0.28]:
                    out = coupled_frailty_metrics(reserve, threshold, coupling=0.5)
                    print(
                        f"{boundary_name:7s} {kind:17s} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} 0.50 "
                        f"{out['mean_reserve']:.6f} {out['min_lane_median']:.6f} {out['resting_ok_frac']:.6f} "
                        f"{out['visible_frac']:.6f} {out['peak_failed_lanes']:.0f} {out['all_lane_failure_frac']:.6f}"
                    )
    print(
        "\nInterpretation key: a non-reducing result would need visible coupled "
        "frailty to reveal multi-lane reserve failure beyond the existing "
        "single-lane phase-defect reserve and to survive finite/random/right "
        "boundary controls."
    )


if __name__ == "__main__":
    main()
