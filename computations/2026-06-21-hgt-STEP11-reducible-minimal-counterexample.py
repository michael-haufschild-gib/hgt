#!/usr/bin/env python3
"""Step 11: minimal counterexample for reducible partial extinction transfer.

Method #16: Use a minimal counterexample.

The candidate vector-survival signal is only non-reducing if partial extinction
is more than a relabeling of the strongest single sigma lane's phase-run
persistence. This script removes one lane at a time and reports whether the
partial/global survival verdict is actually carried by one lane.
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


def max_run(mask: np.ndarray) -> int:
    best = 0
    cur = 0
    for b in mask:
        if b:
            cur += 1
            best = max(best, cur)
        else:
            cur = 0
    return best


def verdict(reserve: np.ndarray, threshold: float, depth: int) -> tuple[np.ndarray, bool, bool, bool]:
    alive = reserve >= threshold
    lane_survive = np.asarray([max_run(row) >= depth for row in alive])
    left = bool(np.any(lane_survive[:2]))
    right = bool(np.any(lane_survive[2:]))
    return lane_survive, bool(np.any(lane_survive)), left, right


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=170)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    sigmas = [0.2, 0.3, 0.5, 0.7]
    windows = [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    thresholds = [0.16, 0.20, 0.28]
    depths = [8, 18, 26, 36]
    print("STEP11 method #16: minimal counterexample to vector partial-extinction novelty")
    print("kind window threshold depth lanes_survive global left right max_runs kill_global_lanes kill_partial_lanes")
    for w_i, window in enumerate(windows):
        for k_i, kind in enumerate(kinds):
            reserve = lane_matrix(kind, sigmas, window, args.samples, primes, seed=20260621 + 997 * w_i + k_i)
            for threshold in thresholds:
                alive = reserve >= threshold
                runs = [max_run(row) for row in alive]
                for depth in depths:
                    lanes, glob, left, right = verdict(reserve, threshold, depth)
                    kill_global = []
                    kill_partial = []
                    for idx, sigma in enumerate(sigmas):
                        kept = np.delete(reserve, idx, axis=0)
                        # Preserve component split by recomputing against remaining
                        kept_alive = kept >= threshold
                        kept_lanes = np.asarray([max_run(row) >= depth for row in kept_alive])
                        kept_glob = bool(np.any(kept_lanes))
                        if glob and not kept_glob:
                            kill_global.append(str(sigma))
                        original_partial = left != right
                        # Rebuild approximate split labels from remaining sigmas.
                        rem_sigmas = [s for j, s in enumerate(sigmas) if j != idx]
                        rem_left = bool(any(ok for ok, s in zip(kept_lanes, rem_sigmas) if s <= 0.3))
                        rem_right = bool(any(ok for ok, s in zip(kept_lanes, rem_sigmas) if s >= 0.5))
                        if original_partial and (rem_left == rem_right):
                            kill_partial.append(str(sigma))
                    if glob or any(r >= 4 for r in runs):
                        print(
                            f"{kind:17s} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} {depth:2d} "
                            f"{''.join('1' if x else '0' for x in lanes)} {int(glob)} {int(left)} {int(right)} "
                            f"{','.join(str(r) for r in runs)} "
                            f"{'none' if not kill_global else ','.join(kill_global)} "
                            f"{'none' if not kill_partial else ','.join(kill_partial)}"
                        )
    print(
        "\nInterpretation key: if one lane kills global/partial survival when removed, "
        "the vector extinction observable reduces to single-lane phase-run persistence."
    )


if __name__ == "__main__":
    main()
