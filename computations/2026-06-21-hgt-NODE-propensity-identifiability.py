#!/usr/bin/env python3
"""THE-MACHINE NODE test: propensity-model identifiability failure.

NODE:
    Identifiability problems can make very different uncertain propensity
    models fit the same observed count data.

Constraint:
    Observed molecule-count histograms do not identify the underlying
    propensity mechanism. A gamma-distributed birth propensity across cells and
    a bursty birth reaction can generate the same negative-binomial count law.
    Extra observations, such as jump-size statistics, are needed to break the
    equivalence.
"""

from __future__ import annotations

import math

import numpy as np


def nb_pmf(kmax: int, r: float, p: float) -> np.ndarray:
    out = np.zeros(kmax + 1)
    for k in range(kmax):
        out[k] = math.exp(
            math.lgamma(k + r)
            - math.lgamma(r)
            - math.lgamma(k + 1)
            + r * math.log(p)
            + k * math.log1p(-p)
        )
    out[-1] = max(0.0, 1.0 - float(np.sum(out[:-1])))
    return out / out.sum()


def empirical_pmf(samples: np.ndarray, kmax: int) -> np.ndarray:
    clipped = np.clip(samples.astype(int), 0, kmax)
    counts = np.bincount(clipped, minlength=kmax + 1).astype(float)
    return counts / counts.sum()


def js_distance(p: np.ndarray, q: np.ndarray) -> float:
    p = p / p.sum()
    q = q / q.sum()
    m = 0.5 * (p + q)

    def kl(a: np.ndarray, b: np.ndarray) -> float:
        mask = a > 0
        return float(np.sum(a[mask] * np.log(a[mask] / b[mask])))

    return math.sqrt(0.5 * kl(p, m) + 0.5 * kl(q, m))


def poisson_gamma_samples(rng: np.random.Generator, n: int, mean: float, shape: float) -> np.ndarray:
    # Extrinsic model: each cell draws a constant birth/death mean theta, then X|theta~Poisson(theta).
    theta = rng.gamma(shape=shape, scale=mean / shape, size=n)
    return rng.poisson(theta)


def burst_samples(rng: np.random.Generator, n: int, r: float, p: float) -> np.ndarray:
    # Bursty model with the same NB law for snapshot counts.
    return rng.negative_binomial(r, p, size=n)


def jump_size_samples(rng: np.random.Generator, n: int, model: str, p: float) -> np.ndarray:
    if model == "extrinsic":
        return np.ones(n, dtype=int)
    if model == "bursty":
        # Geometric burst size on {1,2,...}; p is the NB success parameter.
        return rng.geometric(p, size=n)
    raise ValueError(model)


def main() -> None:
    rng = np.random.default_rng(26062109)
    n = 120_000
    kmax = 80
    mean = 18.0
    shape = 4.5
    p = shape / (shape + mean)
    target = nb_pmf(kmax, shape, p)
    extrinsic = poisson_gamma_samples(rng, n, mean=mean, shape=shape)
    bursty = burst_samples(rng, n, r=shape, p=p)
    pmf_ex = empirical_pmf(extrinsic, kmax)
    pmf_bu = empirical_pmf(bursty, kmax)

    print("NODE validation: count histograms do not identify propensity mechanism")
    print(f"target_NB mean={mean:.3f} shape={shape:.3f} p={p:.5f} n={n}")
    print("model count_mean count_var js_to_target js_to_other q50 q90 q99")
    for name, samples, pmf in [
        ("extrinsic_gamma_propensity", extrinsic, pmf_ex),
        ("bursty_birth_propensity", bursty, pmf_bu),
    ]:
        qs = np.quantile(samples, [0.50, 0.90, 0.99])
        print(
            f"{name:27s} {float(np.mean(samples)):.4f} {float(np.var(samples)):.4f} "
            f"{js_distance(pmf, target):.5f} {js_distance(pmf, pmf_bu if name.startswith('extrinsic') else pmf_ex):.5f} "
            f"{qs[0]:.1f} {qs[1]:.1f} {qs[2]:.1f}"
        )

    print("\nSame endpoint counts, different hidden event structure")
    print("model jump_mean jump_q90 multi_jump_fraction")
    for model in ["extrinsic", "bursty"]:
        jumps = jump_size_samples(rng, n, model, p=p)
        print(
            f"{model:10s} {float(np.mean(jumps)):.4f} "
            f"{float(np.quantile(jumps, 0.90)):.1f} {float(np.mean(jumps > 1)):.4f}"
        )

    # ABC-style ambiguity: sample nearby parameter pairs for both families and
    # count how many pass a count-histogram tolerance.
    accepted = {"extrinsic": 0, "bursty": 0}
    tolerances = []
    for _ in range(240):
        m = rng.uniform(14.0, 22.0)
        r = rng.uniform(2.0, 9.0)
        pp = r / (r + m)
        pmf = empirical_pmf(poisson_gamma_samples(rng, 10_000, m, r), kmax)
        d = js_distance(pmf, target)
        tolerances.append(d)
        if d < 0.035:
            accepted["extrinsic"] += 1
        m = rng.uniform(14.0, 22.0)
        r = rng.uniform(2.0, 9.0)
        pp = r / (r + m)
        pmf = empirical_pmf(burst_samples(rng, 10_000, r, pp), kmax)
        d = js_distance(pmf, target)
        tolerances.append(d)
        if d < 0.035:
            accepted["bursty"] += 1
    print("\nABC histogram-fit ambiguity")
    print(f"accepted_extrinsic={accepted['extrinsic']} accepted_bursty={accepted['bursty']} tolerance=0.035")
    print(f"distance_median={float(np.median(tolerances)):.5f} distance_q10={float(np.quantile(tolerances,0.10)):.5f}")
    print(
        "\nRead: snapshot count data can be fit by two different propensity mechanisms. "
        "The equivalence breaks only after observing event/jump structure, so the "
        "constraint is identifiability of the observation map, not just parameter fitting."
    )


if __name__ == "__main__":
    main()
