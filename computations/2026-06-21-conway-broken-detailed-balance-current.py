#!/usr/bin/env python3
"""THE-MACHINE run: broken detailed balance from maintained reservoirs."""

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


def stationary(P: np.ndarray) -> np.ndarray:
    w, v = np.linalg.eig(P.T)
    idx = int(np.argmin(np.abs(w - 1.0)))
    pi = np.real(v[:, idx])
    pi = np.abs(pi)
    return pi / np.sum(pi)


def current_metrics(P: np.ndarray) -> dict[str, float]:
    pi = stationary(P)
    F = pi[:, None] * P
    J = F - F.T
    cycle = (J[0, 1] + J[1, 2] + J[2, 0]) / 3.0
    return {
        "pi_spread": float(np.max(pi) - np.min(pi)),
        "max_current": float(np.max(np.abs(J))),
        "cycle_current": float(cycle),
        "entropy_prod": float(np.sum(np.where((F > 1e-15) & (F.T > 1e-15), F * np.log(F / F.T), 0.0)) / 2.0),
    }


def node_simulation() -> None:
    balanced = np.asarray(
        [
            [0.70, 0.15, 0.15],
            [0.15, 0.70, 0.15],
            [0.15, 0.15, 0.70],
        ]
    )
    driven = np.asarray(
        [
            [0.70, 0.24, 0.06],
            [0.06, 0.70, 0.24],
            [0.24, 0.06, 0.70],
        ]
    )
    print("NODE simulation: held reservoir affinity breaks detailed balance at steady marginals")
    for name, P in [("balanced", balanced), ("driven", driven)]:
        row = current_metrics(P)
        print(
            f"{name:8s} pi_spread={row['pi_spread']:.6f} max_current={row['max_current']:.6f} "
            f"cycle_current={row['cycle_current']:+.6f} entropy_prod={row['entropy_prod']:.6f}"
        )


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


def lane_sequence(kind: str, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    sigmas = [0.3, 0.5, 0.7]
    seq = []
    for t in np.linspace(window[0], window[1], samples):
        vals = []
        for sigma in sigmas:
            s = complex(float(sigma), float(t))
            vals.append(phase_defect(gamma_part(s), component(kind, s, primes, rng)))
        seq.append(int(np.argmax(vals)))
    return np.asarray(seq, dtype=int)


def transition_matrix(seq: np.ndarray, smooth: float = 0.5) -> np.ndarray:
    counts = np.full((3, 3), smooth, dtype=float)
    for a, b in zip(seq[:-1], seq[1:]):
        counts[int(a), int(b)] += 1.0
    return counts / counts.sum(axis=1, keepdims=True)


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "broken detailed balance caused by held out of equilibrium reservoirs"
    attempts = {
        "A_sigma_lane_cycle_current": "broken detailed balance caused by held sigma lane current reservoirs",
        "B_zero_shadow_cycle_current": "broken detailed balance caused by held zero shadow current reservoirs",
        "C_amplitude_cycle_current": "broken detailed balance caused by held amplitude current reservoirs",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:32s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    print("\nSTEP8/9 HT transfer: sigma-lane detailed-balance current")
    print("kind window pi_spread max_current cycle_current entropy_prod occupancy")
    for window in windows:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(880000 + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
            seq = lane_sequence(kind, window, samples, primes, rng)
            P = transition_matrix(seq)
            row = current_metrics(P)
            occ = np.bincount(seq, minlength=3) / len(seq)
            print(
                f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {row['pi_spread']:.4f} "
                f"{row['max_current']:.5f} {row['cycle_current']:+.5f} {row['entropy_prod']:.5f} "
                f"{occ[0]:.3f},{occ[1]:.3f},{occ[2]:.3f}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=280)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
