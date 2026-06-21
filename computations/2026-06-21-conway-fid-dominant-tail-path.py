#!/usr/bin/env python3
"""FID tail basis: plausible path versus dominant path."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


mp.mp.dps = 100


def normal_tail(x: float) -> float:
    return 0.5 * math.erfc(x / math.sqrt(2.0))


def node_rare_event_path_gap() -> None:
    path_a = normal_tail(5.0)
    path_b = normal_tail(4.4)
    total = path_a + path_b - path_a * path_b
    print("NODE: plausible rare-event path is not proof of dominant path")
    print(f"path_A_threshold=5.0 prob={path_a:.6e} share={path_a / total:.3f}")
    print(f"path_B_threshold=4.4 prob={path_b:.6e} share={path_b / total:.3f}")
    print(
        "constraint: a biased or plausible path must be checked against all "
        "competing paths before it is called dominant"
    )
    print()


def scaled_tail_value(peel: set[int], base: int, n: int) -> mp.mpf:
    s = 2 * n + 1
    peeled = mp.fsum(mp.power(m, -s) for m in peel)
    return (mp.zeta(s) - peeled) * mp.power(base, s)


def hankel_stats(peel: set[int], base: int, size: int) -> tuple[float, float, float]:
    values = {n: scaled_tail_value(peel, base, n) for n in range(1, 2 * size + 1)}
    matrix = np.array(
        [[float(values[i + j + 1]) for j in range(size)] for i in range(size)],
        dtype=float,
    )
    eig = np.linalg.eigvalsh(matrix)
    cond = float(eig[-1] / eig[0]) if eig[0] > 0.0 else math.inf
    return float(eig[0]), float(eig[-1]), cond


def dominance_share(peel: set[int], base: int, n: int) -> tuple[int, float, float]:
    s = 2 * n + 1
    total = scaled_tail_value(peel, base, n)
    least_unpeeled = next(m for m in range(1, 100) if m not in peel)
    base_share = (mp.mpf(1) if base not in peel else mp.mpf(0)) / total
    least_share = mp.power(mp.mpf(base) / least_unpeeled, s) / total
    return least_unpeeled, float(base_share), float(least_share)


def transfer_fid_dominant_path() -> None:
    print("TRANSFER: ResearchNode #18 FID tail-stable certificate")
    print("method #19 write the fake proof")
    print(
        "fake proof: peel previous primes and scale by the next prime; the next "
        "prime tail dominates, so the Hankel certificate is tail-stable"
    )
    print(
        "gap: composites below the next prime are unpeeled competing paths and "
        "may dominate the scaled tail"
    )
    print()

    cases = [
        ("two_tail", {1}, 2),
        ("three_after_12", {1, 2}, 3),
        ("five_prime_only_after_123", {1, 2, 3}, 5),
        ("four_after_123", {1, 2, 3}, 4),
        ("five_after_1234", {1, 2, 3, 4}, 5),
        ("six_after_12345", {1, 2, 3, 4, 5}, 6),
    ]

    print("DOMINANCE CHECK")
    print("case base n least_unpeeled base_share least_unpeeled_share")
    for name, peel, base in cases:
        for n in [1, 5, 10, 20]:
            least, base_share, least_share = dominance_share(peel, base, n)
            print(
                f"{name:27s} {base:02d} {n:02d} {least:02d} "
                f"{base_share:.6f} {least_share:.6f}"
            )
        print()

    print("HANKEL CONDITION CHECK")
    print("case size min_eig max_eig cond")
    for name, peel, base in cases:
        for size in [4, 6, 8, 10]:
            mn, mx, cond = hankel_stats(peel, base, size)
            print(f"{name:27s} {size:02d} {mn:+.4e} {mx:+.4e} {cond:.3e}")
        print()

    print("GATE SUMMARY")
    print(
        "`five_prime_only_after_123` is not a prime-5-dominant tail: by n=20 "
        "the claimed base-5 share is about 0.000106 while the unpeeled composite "
        "4 carries about 0.999894"
    )
    print(
        "FID prime-peeling should be replaced by successor-integer peeling: scale "
        "only by the least unpeeled integer, or peel every integer below the "
        "intended base before claiming a dominant-path certificate"
    )


def main() -> None:
    node_rare_event_path_gap()
    transfer_fid_dominant_path()


if __name__ == "__main__":
    main()
