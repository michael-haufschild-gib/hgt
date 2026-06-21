#!/usr/bin/env python3
"""NODE test: initial measures need entropy/association conditions.

NODE:
    Initial measures must satisfy entropy or association conditions in many
    limit theorems.

Constraint:
    Matching one-site density is not enough. A sequence of initial measures
    must also rule out hidden global correlations or excessive relative
    entropy, otherwise empirical fields need not self-average.
"""

from __future__ import annotations

import math

import numpy as np


SEED = 20260621
REPS = 8000
RHO = 0.5


def kl_bernoulli(p: float, q: float) -> float:
    return p * math.log(p / q) + (1.0 - p) * math.log((1.0 - p) / (1.0 - q))


def sample_product(rng: np.random.Generator, n: int) -> np.ndarray:
    return rng.binomial(n, RHO, size=REPS) / n


def sample_global_mixture(rng: np.random.Generator, n: int, lo: float = 0.2, hi: float = 0.8) -> np.ndarray:
    theta = np.where(rng.random(REPS) < 0.5, lo, hi)
    return rng.binomial(n, theta) / n


def sample_block_mixture(rng: np.random.Generator, n: int, block: int = 50, lo: float = 0.2, hi: float = 0.8) -> np.ndarray:
    blocks = max(1, n // block)
    out = np.zeros(REPS, dtype=float)
    for _ in range(blocks):
        theta = np.where(rng.random(REPS) < 0.5, lo, hi)
        out += rng.binomial(block, theta, size=REPS)
    rem = n - blocks * block
    if rem:
        theta = np.where(rng.random(REPS) < 0.5, lo, hi)
        out += rng.binomial(rem, theta, size=REPS)
    return out / n


def summarize(name: str, samples: np.ndarray, n: int, entropy_density: float, distant_cov_limit: float) -> None:
    var = float(np.var(samples))
    scaled_var = n * var
    q05, q50, q95 = np.quantile(samples, [0.05, 0.50, 0.95])
    print(
        f"{name:18s} N={n:5d} mean={float(np.mean(samples)):.4f} var={var:.6f} "
        f"Nvar={scaled_var:.4f} q05={q05:.4f} q50={q50:.4f} q95={q95:.4f} "
        f"entropy_density={entropy_density:.4f} distant_cov_limit={distant_cov_limit:.4f}"
    )


def main() -> None:
    rng = np.random.default_rng(SEED)
    print("NODE: entropy/association gates for initial measures")
    print(f"seed={SEED} reps={REPS} reference_rho={RHO}")
    print("criterion: same one-site density but bad global correlations should keep O(1) empirical fluctuations")
    mixture_entropy = 0.5 * kl_bernoulli(0.2, RHO) + 0.5 * kl_bernoulli(0.8, RHO)
    block_entropy = mixture_entropy
    global_cov = 0.5 * (0.2 - RHO) ** 2 + 0.5 * (0.8 - RHO) ** 2
    for n in [100, 400, 1600, 6400]:
        summarize("product_good", sample_product(rng, n), n, entropy_density=0.0, distant_cov_limit=0.0)
        summarize("block_mixture", sample_block_mixture(rng, n), n, entropy_density=block_entropy, distant_cov_limit=0.0)
        summarize("global_mixture", sample_global_mixture(rng, n), n, entropy_density=mixture_entropy, distant_cov_limit=global_cov)
    print("\ninterpretation")
    print("Product data has Var(empirical density) ~ 1/N. Global-mixture data has the same mean density but Var stays O(1), exposing why entropy/association assumptions are load-bearing.")


if __name__ == "__main__":
    main()
