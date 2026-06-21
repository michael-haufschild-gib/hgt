#!/usr/bin/env python3
"""THE-MACHINE NODE test: rate-uncertainty propagation in network pruning.

NODE:
    Error propagation from uncertain rate coefficients into pruning decisions.

Constraint:
    A reaction cannot be pruned solely because its nominal-rate importance is
    small. If its rate coefficient is uncertain, the distribution of its output
    importance can cross the pruning threshold. Robust pruning must propagate
    coefficient uncertainty into the decision.

Network:
    A -> B -> C is the target route.
    A -> D -> C is a weak bypass route.
    B -> E is an off-target loss route.
"""

from __future__ import annotations

import numpy as np


REACTIONS = ("A_to_B", "B_to_C", "A_to_D", "D_to_C", "B_to_E")
NOMINAL = np.array([1.00, 0.82, 0.035, 0.055, 0.032], dtype=float)


def integrate(rates: np.ndarray, steps: int = 320, dt: float = 0.018) -> np.ndarray:
    rates = np.atleast_2d(rates).astype(float)
    n = rates.shape[0]
    state = np.zeros((n, 5), dtype=float)
    state[:, 0] = 1.0
    for _ in range(steps):
        a, b, c, d, e = state.T
        r1 = rates[:, 0] * a
        r2 = rates[:, 1] * b
        r3 = rates[:, 2] * a
        r4 = rates[:, 3] * d
        r5 = rates[:, 4] * b
        state[:, 0] += dt * (-r1 - r3)
        state[:, 1] += dt * (r1 - r2 - r5)
        state[:, 2] += dt * (r2 + r4)
        state[:, 3] += dt * (r3 - r4)
        state[:, 4] += dt * r5
        state = np.maximum(state, 0.0)
    return state


def importance_distribution(rates: np.ndarray, observable: str) -> np.ndarray:
    full = integrate(rates)
    target_idx = 2 if observable == "C" else 4
    denom = np.maximum(np.abs(full[:, target_idx]), 1e-12)
    out = []
    for j in range(len(REACTIONS)):
        pruned_rates = np.array(rates, copy=True)
        pruned_rates[:, j] = 0.0
        pruned = integrate(pruned_rates)
        rel = np.abs(full[:, target_idx] - pruned[:, target_idx]) / denom
        out.append(rel)
    return np.vstack(out).T


def sample_rates(rng: np.random.Generator, n: int, sigma: np.ndarray, corr: float = 0.0) -> np.ndarray:
    cov = np.diag(sigma * sigma)
    if corr:
        for i in range(len(sigma)):
            for j in range(len(sigma)):
                if i != j:
                    cov[i, j] = corr * sigma[i] * sigma[j]
    draws = rng.multivariate_normal(np.zeros(len(sigma)), cov, size=n)
    return NOMINAL[None, :] * np.exp(draws)


def summarize_case(label: str, sigma: np.ndarray, corr: float, threshold: float, rng: np.random.Generator) -> None:
    rates = sample_rates(rng, 5000, sigma=sigma, corr=corr)
    imp_c = importance_distribution(rates, "C")
    imp_e = importance_distribution(rates, "E")
    imp_joint = np.maximum(imp_c, imp_e)

    nominal = NOMINAL[None, :]
    nom_c = importance_distribution(nominal, "C")[0]
    nom_e = importance_distribution(nominal, "E")[0]
    nom_joint = np.maximum(nom_c, nom_e)

    print(f"\nCASE {label}: threshold={threshold} corr={corr}")
    print("reaction nominal_C nominal_E nominal_joint q50_joint q90_joint q99_joint fail_prob prune_nominal")
    for i, name in enumerate(REACTIONS):
        q50, q90, q99 = np.quantile(imp_joint[:, i], [0.50, 0.90, 0.99])
        fail = float(np.mean(imp_joint[:, i] > threshold))
        prune_nom = int(nom_joint[i] < threshold)
        print(
            f"{name:7s} {nom_c[i]:.4f} {nom_e[i]:.4f} {nom_joint[i]:.4f} "
            f"{q50:.4f} {q90:.4f} {q99:.4f} {fail:.3f} {prune_nom}"
        )

    nominal_prune = nom_joint < threshold
    robust_prune = np.quantile(imp_joint, 0.95, axis=0) < threshold
    print(
        "decision_summary "
        f"nominal_pruned={[REACTIONS[i] for i in np.where(nominal_prune)[0]]} "
        f"robust_pruned={[REACTIONS[i] for i in np.where(robust_prune)[0]]}"
    )


def main() -> None:
    rng = np.random.default_rng(26062115)
    threshold = 0.08
    print("NODE validation: uncertain rate coefficients alter pruning decisions")
    print("Species order: A,B,C,D,E. Observables: target C and off-target E.")
    print("Constraint: prune by propagated importance quantiles, not nominal point estimates.")
    summarize_case(
        "low_uncertainty_control",
        sigma=np.array([0.05, 0.05, 0.05, 0.05, 0.05]),
        corr=0.0,
        threshold=threshold,
        rng=rng,
    )
    summarize_case(
        "high_minor_uncertainty",
        sigma=np.array([0.05, 0.05, 1.10, 1.10, 1.15]),
        corr=0.0,
        threshold=threshold,
        rng=rng,
    )
    summarize_case(
        "correlated_minor_uncertainty",
        sigma=np.array([0.05, 0.05, 0.95, 0.95, 1.05]),
        corr=0.55,
        threshold=threshold,
        rng=rng,
    )
    print(
        "\nRead: under low uncertainty, nominal and robust pruning agree. When minor rates "
        "are uncertain, nominally prunable reactions acquire high-tail importance and "
        "must be retained by a quantile-aware pruning rule."
    )


if __name__ == "__main__":
    main()
