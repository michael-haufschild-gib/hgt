#!/usr/bin/env python3
"""Workflow W8: spin-orbit coupling requires matrix-valued boundary data."""

from __future__ import annotations

import argparse
import math
import random

import mpmath as mp


def matmul(a: list[list[complex]], b: list[list[complex]]) -> list[list[complex]]:
    return [
        [sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)]
        for i in range(2)
    ]


def matdag(a: list[list[complex]]) -> list[list[complex]]:
    return [[a[j][i].conjugate() for j in range(2)] for i in range(2)]


def trace(a: list[list[complex]]) -> complex:
    return a[0][0] + a[1][1]


def ident() -> list[list[complex]]:
    return [[1.0 + 0.0j, 0.0j], [0.0j, 1.0 + 0.0j]]


def ry(theta: float) -> list[list[complex]]:
    c = math.cos(theta / 2.0)
    s = math.sin(theta / 2.0)
    return [[c + 0.0j, -s + 0.0j], [s + 0.0j, c + 0.0j]]


def matadd(a: list[list[complex]], b: list[list[complex]]) -> list[list[complex]]:
    return [[a[i][j] + b[i][j] for j in range(2)] for i in range(2)]


def matscale(z: complex, a: list[list[complex]]) -> list[list[complex]]:
    return [[z * a[i][j] for j in range(2)] for i in range(2)]


def unpolarized_transport(delta: float, theta: float) -> float:
    amp = matadd(ident(), matscale(complex(math.cos(delta), math.sin(delta)), ry(theta)))
    return float((trace(matmul(matdag(amp), amp)).real) / 8.0)


def spin_z_after_rotation(theta: float) -> float:
    # Inject spin-up |0>; R_y(theta) gives <sigma_z> = cos(theta).
    return math.cos(theta)


def node_simulation() -> None:
    print("NODE: spin-orbit coupling needs matrix-valued boundary conditions")
    print("theta visibility scalar_visibility spin_z_after scalar_spin_z min_T max_T")
    for theta in [0.0, math.pi / 4.0, math.pi / 2.0, 3.0 * math.pi / 4.0, math.pi]:
        vals = [unpolarized_transport(2.0 * math.pi * i / 720.0, theta) for i in range(720)]
        max_t = max(vals)
        min_t = min(vals)
        visibility = (max_t - min_t) / max(max_t + min_t, 1e-12)
        print(
            f"{theta:7.4f} {visibility:10.5f} {1.0:17.5f} "
            f"{spin_z_after_rotation(theta):12.5f} {1.0:13.5f} {min_t:9.5f} {max_t:9.5f}"
        )


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def first_primes(n: int) -> list[int]:
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
    return primes


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 2e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: list[int]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def matrix_transport(g: complex, p: complex, theta: float) -> float:
    # Matrix analogue of two coherent paths: g*I + p*R_y(theta).
    amp = matadd(matscale(g, ident()), matscale(p, ry(theta)))
    return float((trace(matmul(matdag(amp), amp)).real) / 2.0)


def scalar_transport(g: complex, p: complex) -> float:
    return abs(g + p) ** 2


def corr(xs: list[float], ys: list[float]) -> float:
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    if vx <= 1e-30 or vy <= 1e-30:
        return 0.0
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(vx * vy)


def ht_transfer(samples: int, prime_count: int, seed: int) -> None:
    node_sig = "spin orbit coupling needs matrix valued boundary conditions"
    candidates = [
        "gamma prime coupling needs matrix valued boundary diagnostics",
        "scalar seam conditions miss matrix weld transport",
        "spinor boundary representation of archimedean prime weld",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best: tuple[int, int, str] | None = None
    for idx, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{idx} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, idx, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")

    primes = first_primes(prime_count)
    rng = random.Random(seed)
    print("\nSTEP9 method=17 change representation: scalar vs matrix weld diagnostic")
    print("kind sigma theta corr_scalar_matrix mean_log_ratio low_matrix_rate")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            scalar_vals: list[float] = []
            matrix_vals: dict[float, list[float]] = {math.pi / 2.0: [], math.pi: []}
            for i in range(samples):
                t = 80.0 + 0.06 * i
                s = complex(float(sigma), t)
                g = gamma_part(s)
                z = dlog_zeta(s)
                f = dlog_finite_euler(s, primes)
                phase = rng.uniform(-math.pi, math.pi)
                r = abs(z) * complex(math.cos(phase), math.sin(phase))
                p = z if kind == "true" else f if kind == "finite" else r
                scalar_vals.append(scalar_transport(g, p))
                for theta in matrix_vals:
                    matrix_vals[theta].append(matrix_transport(g, p, theta))
            for theta, vals in matrix_vals.items():
                ratios = [math.log((v + 1e-300) / (u + 1e-300)) for u, v in zip(scalar_vals, vals)]
                cutoff = sorted(vals)[int(0.10 * (samples - 1))]
                low_rate = sum(v <= cutoff for v in vals) / samples
                print(
                    f"{kind:6s} {sigma:.1f} {theta:5.2f} {corr(scalar_vals, vals):18.5f} "
                    f"{sum(ratios)/samples:14.5f} {low_rate:15.5f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=850)
    parser.add_argument("--prime-count", type=int, default=80)
    parser.add_argument("--seed", type=int, default=492832716409134168 % (2**32))
    args = parser.parse_args()
    node_simulation()
    ht_transfer(args.samples, args.prime_count, args.seed + 7)


if __name__ == "__main__":
    main()
