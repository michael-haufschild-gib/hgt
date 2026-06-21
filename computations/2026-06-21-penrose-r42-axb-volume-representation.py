#!/usr/bin/env python3
"""R42: Lyapunov tangent-volume transfer to affine ax+b boundary modes.

NODE: volume contraction over a relevant tangent subspace is the sum of
Lyapunov exponents on that subspace.

Target: affine ax+b geometry / universal curvature.  For a finite boundary
mode block S, the archimedean generator is diagonal:

    D e_m = -(m . log p) e_m.

So the determinant-line contraction is the trace:

    tr(D|S) = -sum_{m in S} m . log p.

This script checks the induced representation numerically and searches for
distinct finite blocks with the same determinant character but different
shape statistics.
"""

from __future__ import annotations

from itertools import combinations, product
from math import log
from typing import Iterable, List, Sequence, Tuple

Vector = Tuple[int, ...]
Block = Tuple[Vector, ...]

PRIMES = (2, 3, 5)
LOGS = tuple(log(p) for p in PRIMES)


def vadd(a: Vector, b: Vector) -> Vector:
    return tuple(x + y for x, y in zip(a, b))


def vsum(block: Block) -> Vector:
    total = (0,) * len(PRIMES)
    for v in block:
        total = vadd(total, v)
    return total


def dot_logs(v: Vector) -> float:
    return sum(x * ell for x, ell in zip(v, LOGS))


def trace_D(block: Block) -> float:
    return -sum(dot_logs(v) for v in block)


def det_sigma_exponents(block: Block) -> Vector:
    """det(sigma_p | block) = product_p p^{-exponent_p}."""
    return vsum(block)


def shift_block(block: Block, prime_index: int) -> Block:
    shifted = []
    for v in block:
        w = list(v)
        w[prime_index] += 1
        shifted.append(tuple(w))
    return tuple(shifted)


def covariance_shape(block: Block) -> Tuple[float, float, float]:
    """Small shape fingerprint invisible to the determinant line."""
    k = len(block)
    dim = len(PRIMES)
    mean = [sum(v[i] for v in block) / k for i in range(dim)]
    centered = [[v[i] - mean[i] for i in range(dim)] for v in block]
    variances = [sum(row[i] * row[i] for row in centered) / k for i in range(dim)]
    pair_sq = 0.0
    pair_count = 0
    for a, b in combinations(block, 2):
        pair_sq += sum((x - y) ** 2 for x, y in zip(a, b))
        pair_count += 1
    avg_pair_sq = pair_sq / pair_count if pair_count else 0.0
    return (sum(variances), max(variances), avg_pair_sq)


def all_modes(max_coord: int = 3, max_weight: int = 4) -> List[Vector]:
    modes = []
    for v in product(range(max_coord + 1), repeat=len(PRIMES)):
        if 0 <= sum(v) <= max_weight:
            modes.append(v)
    return modes


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def format_block(block: Block) -> str:
    return "{" + ", ".join(str(v) for v in block) + "}"


def find_collisions(k: int = 3, limit: int = 8) -> List[Tuple[Tuple[int, Vector], Block, Block]]:
    by_passport = {}
    modes = all_modes()
    for block in combinations(modes, k):
        passport = (k, vsum(block))
        by_passport.setdefault(passport, []).append(block)

    collisions = []
    for passport, blocks in by_passport.items():
        if len(blocks) < 2:
            continue
        shapes = {}
        for block in blocks:
            shapes.setdefault(covariance_shape(block), block)
        if len(shapes) < 2:
            continue
        shape_items = list(shapes.items())
        a = shape_items[0][1]
        b = max(shape_items[1:], key=lambda item: abs(item[0][0] - shape_items[0][0][0]))[1]
        collisions.append((passport, a, b))
        if len(collisions) >= limit:
            break
    return collisions


def fiber_statistics(max_k: int = 5) -> None:
    modes = all_modes()
    print("\nInvariant-fiber statistics:")
    for k in range(2, max_k + 1):
        by_passport = {}
        for block in combinations(modes, k):
            passport = (k, vsum(block))
            by_passport.setdefault(passport, []).append(block)

        nontrivial = [blocks for blocks in by_passport.values() if len(blocks) > 1]
        max_fiber = max((len(blocks) for blocks in nontrivial), default=1)
        max_shape_spread = 0.0
        max_trace_error = 0.0
        for blocks in nontrivial:
            shape_values = [covariance_shape(block)[0] for block in blocks]
            max_shape_spread = max(max_shape_spread, max(shape_values) - min(shape_values))
            traces = [trace_D(block) for block in blocks]
            max_trace_error = max(max_trace_error, max(traces) - min(traces))
        print(
            f"  k={k}: passports={len(by_passport)}, "
            f"nontrivial_fibers={len(nontrivial)}, max_fiber={max_fiber}, "
            f"max_shape_spread={max_shape_spread:.6f}, "
            f"max_trace_spread={max_trace_error:.3e}"
        )


def main() -> None:
    attempts = [
        "tr(D on S) = -sum_{m in S} m.logp",
        "det(sigma_p on S) = p^{-sum_{m in S} m_p}",
        "affine determinant loop = universal curvature area times dim(S)",
    ]
    node = "volume contraction equals the sum of Lyapunov exponents on the tangent subspace"
    print("R42 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    blocks = [
        ((0, 0, 0), (2, 0, 0), (0, 2, 0)),
        ((1, 0, 0), (0, 1, 0), (1, 1, 0)),
    ]
    print("\nHand checks:")
    for block in blocks:
        print(f"  block={format_block(block)}")
        print(f"    determinant passport k,sum={len(block)},{det_sigma_exponents(block)}")
        print(f"    trace_D={trace_D(block): .12f}")
        print(f"    shape variance,maxvar,avg_pair_sq={covariance_shape(block)}")

    print("\nUniversal determinant-curvature shift check:")
    base = ((0, 0, 0), (2, 0, 0), (0, 2, 0))
    for i, p in enumerate(PRIMES):
        shifted = shift_block(base, i)
        delta = trace_D(shifted) - trace_D(base)
        predicted = -len(base) * LOGS[i]
        print(
            f"  shift by e_{p}: delta_trace={delta: .12f}, "
            f"-dim(S)log({p})={predicted: .12f}"
        )

    print("\nCollision search: same determinant passport, different shape")
    for passport, a, b in find_collisions():
        print(f"  passport={passport}")
        print(f"    A={format_block(a)}")
        print(f"      trace_D={trace_D(a): .12f}, shape={covariance_shape(a)}")
        print(f"    B={format_block(b)}")
        print(f"      trace_D={trace_D(b): .12f}, shape={covariance_shape(b)}")

    fiber_statistics()

    print("\nInterpretation:")
    print("  The determinant line factors through only (dim S, sum_{m in S} m).")
    print("  Distinct mode geometries with different covariance/mixing shape can have")
    print("  exactly the same affine tangent-volume contraction.")


if __name__ == "__main__":
    main()
