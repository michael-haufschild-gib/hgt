#!/usr/bin/env python3
"""THE-MACHINE run: high-dimensional fitness landscapes and corank one-number shadows."""

from __future__ import annotations

import argparse
import itertools
import math

import mpmath as mp
import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_fitness_dimension() -> None:
    print("NODE simulation: high-dimensional fitness spaces mislead 2D/3D diagrams")
    print("dims projected_best_rank true_best_rank projected_gap hidden_epistasis")
    rng = np.random.default_rng(190411)
    for dims in [4, 8, 16, 32]:
        n = 3000
        genotypes = rng.integers(0, 2, size=(n, dims))
        weights = rng.normal(0.0, 1.0, dims)
        # Hidden epistasis in omitted coordinates.
        epi = np.zeros(n)
        for i in range(2, dims - 1, 2):
            epi += 0.7 * (genotypes[:, i] == genotypes[:, i + 1])
        fitness = genotypes @ weights + epi
        projected = genotypes[:, :2] @ weights[:2]
        projected_best = int(np.argmax(projected))
        true_best = int(np.argmax(fitness))
        projected_rank_of_true = int(np.sum(projected > projected[true_best]) + 1)
        true_rank_of_projected = int(np.sum(fitness > fitness[projected_best]) + 1)
        gap = float(np.max(fitness) - fitness[projected_best])
        hidden = float(np.std(epi) / max(np.std(fitness), 1e-12))
        print(f"{dims:4d} {projected_rank_of_true:19d} {true_rank_of_projected:14d} {gap:13.4f} {hidden:15.4f}")


def run_levenshtein() -> str:
    node_sig = "dimensionality of genotype phenotype spaces makes visual intuitions misleading"
    candidates = [
        "corank one number shadow hides value arithmeticity dimension",
        "seam one number hides algebraic dimension behind linear corank",
        "linear corank landscape hides high dimensional value relations",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best = None
    for i, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{i} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, i, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")
    return best[2]


def relation_search(values, monomials, height: int):
    nums = [mp.mpf(f(values)) for f in monomials]
    best = (mp.inf, None)
    for coeffs in itertools.product(range(-height, height + 1), repeat=len(nums)):
        if not any(coeffs):
            continue
        # Skip all-zero constant-free degeneracy automatically by value.
        val = mp.fsum(c * x for c, x in zip(coeffs, nums))
        err = abs(val)
        if err < best[0]:
            best = (err, coeffs)
    return best


def ht_corank_shadow(height: int) -> None:
    mp.mp.dps = 80
    algebraic = {"a": mp.sqrt(2), "b": mp.sqrt(3)}
    generic = {"a": mp.e, "b": mp.pi}
    linear_monomials = [
        lambda v: mp.mpf(1),
        lambda v: v["a"],
        lambda v: v["b"],
    ]
    quadratic_monomials = linear_monomials + [
        lambda v: v["a"] * v["a"],
        lambda v: v["a"] * v["b"],
        lambda v: v["b"] * v["b"],
    ]
    print("\nStanding-order consolidated target: corank infinity-minus-one, seam as one number")
    print("STEP8 transfer: corank one-number shadow hides value-arithmeticity dimension")
    print("STEP9 method 1: split into subclaims")
    print("Subclaim A: linear relation search sees both examples as rank-2 over Q at small height.")
    print("Subclaim B: quadratic relation search separates algebraic from generic-looking values.")
    print("Subclaim C: therefore one-number linear corank is blind to value-arithmeticity.")
    print(f"height={height}")
    print("case linear_best_err linear_coeffs quadratic_best_err quadratic_coeffs")
    for name, vals in [("algebraic", algebraic), ("generic", generic)]:
        lin_err, lin_coeffs = relation_search(vals, linear_monomials, height)
        quad_err, quad_coeffs = relation_search(vals, quadratic_monomials, height)
        print(f"{name:9s} {float(lin_err):15.6e} {lin_coeffs!s:18s} {float(quad_err):18.6e} {quad_coeffs}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--height", type=int, default=4)
    args = parser.parse_args()
    node_fitness_dimension()
    run_levenshtein()
    print("\nSTEP7 formula check: fitness projection/rank formulas are NODE-side diagnostics. Unchanged use is corank-blind and not promoted.")
    ht_corank_shadow(args.height)


if __name__ == "__main__":
    main()
