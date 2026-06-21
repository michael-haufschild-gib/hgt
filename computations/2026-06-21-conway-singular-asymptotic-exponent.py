#!/usr/bin/env python3
"""THE-MACHINE run: singular models break asymptotic geometry.

Random path:
    Information geometry -> singular models break standard asymptotic
    geometric intuitions.

NODE constraint:
    The regular Fisher/Laplace picture requires a nondegenerate quadratic
    local loss. A singular model has a flatter local loss, so the sublevel
    volume and the partition integral scale with a nonstandard exponent.

STEP 9 method #3:
    Reverse it. Instead of only testing "singular geometry => broken
    asymptotics", estimate the exponent and ask whether a broken exponent
    diagnoses a singular/flat constraint.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

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


def integral_z(n: float, delta: float) -> float:
    """Z_n(delta)=int exp(-n(delta*x^2+x^4)) dx on R."""
    mp.mp.dps = 40
    n_mp = mp.mpf(str(n))
    delta_mp = mp.mpf(str(delta))
    f = lambda x: mp.e ** (-n_mp * (delta_mp * x * x + x**4))
    return float(mp.quad(f, [-mp.inf, mp.inf]))


def apparent_exponent(z1: float, z2: float, n1: float, n2: float) -> float:
    return -float((math.log(z2) - math.log(z1)) / (math.log(n2) - math.log(n1)))


def node_simulation() -> None:
    print("NODE simulation: singular local loss changes Laplace/asymptotic exponent")
    print("loss_delta Z(1e2) Z(1e4) Z(1e6) alpha_1e2_1e4 alpha_1e4_1e6")
    for delta in [1.0, 0.1, 0.01, 0.0]:
        ns = [1e2, 1e4, 1e6]
        zs = [integral_z(n, delta) for n in ns]
        a1 = apparent_exponent(zs[0], zs[1], ns[0], ns[1])
        a2 = apparent_exponent(zs[1], zs[2], ns[1], ns[2])
        print(f"{delta:9.3g} {zs[0]:.8e} {zs[1]:.8e} {zs[2]:.8e} {a1:.4f} {a2:.4f}")
    print("reverse read: exponent near 1/2 diagnoses regular quadratic loss; 1/4 diagnoses a quartic singularity")


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


def phase_loss(g: complex, p: complex) -> float:
    """Small loss means the archimedean and prime-side vectors nearly cancel."""
    return float(abs(g + p) / max(abs(g), abs(p), 1e-300))


@dataclass(frozen=True)
class ExponentRow:
    alpha: float
    mass_025: float
    mass_050: float
    mass_075: float
    mass_100: float
    median_loss: float
    q10_loss: float


def sublevel_exponent(losses: np.ndarray, eps_grid: np.ndarray) -> ExponentRow:
    masses = np.asarray([np.mean(losses <= eps) for eps in eps_grid], dtype=float)
    mask = (masses > 0.005) & (masses < 0.995)
    if int(np.sum(mask)) >= 2:
        alpha, _ = np.polyfit(np.log(eps_grid[mask]), np.log(masses[mask]), 1)
    else:
        alpha = float("nan")
    return ExponentRow(
        alpha=float(alpha),
        mass_025=float(np.mean(losses <= 0.25)),
        mass_050=float(np.mean(losses <= 0.50)),
        mass_075=float(np.mean(losses <= 0.75)),
        mass_100=float(np.mean(losses <= 1.00)),
        median_loss=float(np.median(losses)),
        q10_loss=float(np.quantile(losses, 0.10)),
    )


def losses_for(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> np.ndarray:
    losses = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p = component(kind, s, primes, rng)
        losses.append(phase_loss(g, p))
    return np.asarray(losses, dtype=float)


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "loss delta theta squared plus theta fourth sublevel volume exponent"
    attempts = {
        "A_phase_loss_sublevel_exponent": "loss phase cancellation sublevel volume exponent",
        "B_taylor_remainder_order_exponent": "loss continuum derivative taylor remainder order exponent",
        "C_fisher_wall_distance_exponent": "loss fisher sigma wall distance metric exponent",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:34s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    eps_grid = np.asarray([0.18, 0.25, 0.35, 0.50, 0.70, 1.00, 1.35], dtype=float)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    sigmas = [0.2, 0.3, 0.5, 0.7, 0.9, 1.2]
    print("\nSTEP8/9 HT transfer: phase-loss sublevel exponent")
    print(f"samples={samples} finite_prime_count={prime_count}")
    print("kind sigma window alpha mass<=.25 mass<=.50 mass<=.75 mass<=1 median_loss q10_loss")
    for sigma in sigmas:
        for window in windows:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(880000 + int(100 * sigma) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
                losses = losses_for(kind, sigma, window, samples, primes, rng)
                row = sublevel_exponent(losses, eps_grid)
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{row.alpha:.4f} {row.mass_025:.3f} {row.mass_050:.3f} {row.mass_075:.3f} "
                    f"{row.mass_100:.3f} {row.median_loss:.4f} {row.q10_loss:.4f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
