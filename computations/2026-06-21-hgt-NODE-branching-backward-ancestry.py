#!/usr/bin/env python3
"""THE-MACHINE NODE test: backward ancestry differs from forward growth.

NODE:
    Backward-in-time ancestry differs from forward-in-time population growth,
    especially under conditioning on survival.

Constraint:
    When a terminal surviving individual is sampled, its ancestral line is not
    distributed like a random forward parent. Ancestors are weighted by how many
    descendants they leave. For a Galton-Watson step this gives the size-biased
    offspring law P*(K=k)=k P(K=k)/E[K].

Tests:
    - existence: sampled terminal spines are close to the size-biased law and
      far from the original offspring law;
    - non-existence/control: direct event-level offspring draws match the
      original law, not the size-biased law;
    - driving force: the spine lift grows with offspring variance.
"""

from __future__ import annotations

import math
from collections.abc import Callable

import numpy as np


def tv_distance(a: np.ndarray, b: np.ndarray) -> float:
    n = max(len(a), len(b))
    aa = np.zeros(n)
    bb = np.zeros(n)
    aa[: len(a)] = a
    bb[: len(b)] = b
    return 0.5 * float(np.sum(np.abs(aa - bb)))


def empirical_pmf(samples: list[int] | np.ndarray, kmax: int) -> np.ndarray:
    arr = np.asarray(samples, dtype=int)
    clipped = np.clip(arr, 0, kmax)
    counts = np.bincount(clipped, minlength=kmax + 1).astype(float)
    return counts / max(1.0, float(np.sum(counts)))


def binomial_pmf(n: int, p: float, kmax: int) -> np.ndarray:
    out = np.zeros(kmax + 1)
    for k in range(min(n, kmax) + 1):
        out[k] = math.comb(n, k) * (p**k) * ((1.0 - p) ** (n - k))
    return out / out.sum()


def poisson_pmf(mean: float, kmax: int) -> np.ndarray:
    out = np.zeros(kmax + 1)
    out[0] = math.exp(-mean)
    for k in range(1, kmax + 1):
        out[k] = out[k - 1] * mean / k
    out[-1] += max(0.0, 1.0 - float(out.sum()))
    return out / out.sum()


def geometric_pmf(mean: float, kmax: int) -> np.ndarray:
    # Failures before first success, support {0,1,2,...}, mean=(1-p)/p.
    p = 1.0 / (1.0 + mean)
    out = np.array([p * ((1.0 - p) ** k) for k in range(kmax + 1)], dtype=float)
    out[-1] += max(0.0, 1.0 - float(out.sum()))
    return out / out.sum()


def size_biased_pmf(pmf: np.ndarray) -> np.ndarray:
    k = np.arange(len(pmf), dtype=float)
    mean = float(np.dot(k, pmf))
    out = k * pmf / mean
    return out / out.sum()


def simulate_spines(
    rng: np.random.Generator,
    draw: Callable[[int], np.ndarray],
    trials: int,
    horizon: int,
    max_pop: int,
) -> tuple[np.ndarray, int, int]:
    lineage_counts: list[int] = []
    survived = 0
    capped = 0
    for _ in range(trials):
        parents_by_gen: list[np.ndarray] = []
        offspring_by_gen: list[np.ndarray] = []
        pop = 1
        alive = True
        for _gen in range(horizon):
            offspring = draw(pop).astype(int)
            total = int(offspring.sum())
            if total == 0:
                alive = False
                break
            if total > max_pop:
                capped += 1
                alive = False
                break
            parents = np.repeat(np.arange(pop, dtype=int), offspring)
            offspring_by_gen.append(offspring)
            parents_by_gen.append(parents)
            pop = total
        if not alive:
            continue
        survived += 1
        child = int(rng.integers(pop))
        path_counts: list[int] = []
        for gen in range(horizon - 1, -1, -1):
            parent = int(parents_by_gen[gen][child])
            path_counts.append(int(offspring_by_gen[gen][parent]))
            child = parent
        lineage_counts.extend(path_counts)
    return np.asarray(lineage_counts, dtype=int), survived, capped


def summarize_case(
    name: str,
    mean: float,
    variance: float,
    pmf: np.ndarray,
    direct_draw: Callable[[int], np.ndarray],
    spine_draw: Callable[[int], np.ndarray],
    rng: np.random.Generator,
) -> None:
    kmax = len(pmf) - 1
    size_pmf = size_biased_pmf(pmf)
    original_mean = float(np.dot(np.arange(kmax + 1), pmf))
    size_mean = float(np.dot(np.arange(kmax + 1), size_pmf))
    direct = direct_draw(120_000)
    direct_pmf = empirical_pmf(direct, kmax)
    spines, survived, capped = simulate_spines(
        rng=rng,
        draw=spine_draw,
        trials=2400,
        horizon=14,
        max_pop=35_000,
    )
    spine_pmf = empirical_pmf(spines, kmax)
    direct_mean = float(np.mean(direct))
    spine_mean = float(np.mean(spines)) if len(spines) else 0.0
    print(
        f"{name:10s} mean={mean:.3f} variance={variance:.3f} "
        f"survived={survived:4d} capped={capped:3d} "
        f"direct_mean={direct_mean:.4f} spine_mean={spine_mean:.4f} "
        f"theory_original={original_mean:.4f} theory_sizebiased={size_mean:.4f}"
    )
    print(
        f"{'':10s} TV(direct,original)={tv_distance(direct_pmf, pmf):.4f} "
        f"TV(direct,sizebiased)={tv_distance(direct_pmf, size_pmf):.4f} "
        f"TV(spine,original)={tv_distance(spine_pmf, pmf):.4f} "
        f"TV(spine,sizebiased)={tv_distance(spine_pmf, size_pmf):.4f} "
        f"lift={spine_mean - original_mean:.4f} theory_lift={variance / mean:.4f}"
    )


def main() -> None:
    rng = np.random.default_rng(26062119)
    target_mean = 1.30
    print("NODE validation: backward ancestry is size-biased under survival conditioning")
    print("All cases have comparable mean; variance should drive the backward-spine lift.")
    print(
        "case       mean variance survived capped direct_mean spine_mean "
        "theory_original theory_sizebiased"
    )

    n, p = 4, target_mean / 4.0
    summarize_case(
        "binomial",
        mean=target_mean,
        variance=n * p * (1.0 - p),
        pmf=binomial_pmf(n, p, 18),
        direct_draw=lambda m: rng.binomial(n, p, size=m),
        spine_draw=lambda m: rng.binomial(n, p, size=m),
        rng=rng,
    )

    summarize_case(
        "poisson",
        mean=target_mean,
        variance=target_mean,
        pmf=poisson_pmf(target_mean, 18),
        direct_draw=lambda m: rng.poisson(target_mean, size=m),
        spine_draw=lambda m: rng.poisson(target_mean, size=m),
        rng=rng,
    )

    geo_mean = target_mean
    geo_p = 1.0 / (1.0 + geo_mean)
    summarize_case(
        "geometric",
        mean=geo_mean,
        variance=(1.0 - geo_p) / (geo_p**2),
        pmf=geometric_pmf(geo_mean, 18),
        direct_draw=lambda m: rng.geometric(geo_p, size=m) - 1,
        spine_draw=lambda m: rng.geometric(geo_p, size=m) - 1,
        rng=rng,
    )

    print(
        "\nRead: direct forward event samples stay near the original law, while "
        "terminal backward spines move toward the size-biased law. The lift "
        "tracks variance/mean, so survival-conditioned ancestry is an active "
        "constraint, not a cosmetic relabeling of forward growth."
    )


if __name__ == "__main__":
    main()
