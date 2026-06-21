#!/usr/bin/env python3
"""THE-MACHINE NODE test: absolute irreversibility in fluctuation theorems.

NODE:
    Absolute irreversibility matters when reverse trajectories have zero
    probability.

Constraint:
    A forward process can place positive probability on trajectories that are
    outside the support of the reverse protocol. Then the ordinary integral
    fluctuation identity misses a singular probability mass lambda, and the
    corrected identity is <exp(-sigma)> = 1 - lambda.
"""

from __future__ import annotations

import numpy as np


def node_case(label: str, forward: np.ndarray, reverse: np.ndarray) -> None:
    forward = forward / forward.sum()
    reverse = reverse / reverse.sum()
    support = forward > 0
    singular_lambda = float(reverse[~support].sum())
    finite_part = float(np.sum(forward[support] * reverse[support] / forward[support]))
    ordinary_claim = 1.0
    corrected = 1.0 - singular_lambda
    finite_entropy = float(np.sum(forward[support] * np.log(forward[support] / reverse[support])))
    print(
        f"{label:18s} lambda={singular_lambda:.4f} "
        f"<exp(-sigma)>_finite={finite_part:.4f} corrected={corrected:.4f} "
        f"ordinary_error={abs(finite_part - ordinary_claim):.4f} "
        f"finite_entropy={finite_entropy:.4f}"
    )


def random_support_sweep(rng: np.random.Generator) -> None:
    print("\nSupport-loss sweep")
    print("dropped_forward_states lambda finite_identity corrected")
    reverse = rng.dirichlet(np.ones(12))
    for dropped in [0, 1, 2, 4, 7, 10]:
        forward = rng.dirichlet(np.ones(12))
        if dropped:
            idx = np.argsort(forward)[:dropped]
            forward[idx] = 0.0
        forward = forward / forward.sum()
        support = forward > 0
        lam = float(reverse[~support].sum())
        finite = float(np.sum(forward[support] * reverse[support] / forward[support]))
        print(f"{dropped:22d} {lam:.4f} {finite:.4f} {1.0 - lam:.4f}")


def main() -> None:
    print("NODE validation: absolute irreversibility changes the integral fluctuation identity")
    print("case lambda <exp(-sigma)>_finite corrected ordinary_error finite_entropy")
    node_case(
        "full_support",
        np.asarray([0.15, 0.25, 0.35, 0.25]),
        np.asarray([0.20, 0.30, 0.10, 0.40]),
    )
    node_case(
        "one_impossible_rev",
        np.asarray([0.15, 0.25, 0.00, 0.60]),
        np.asarray([0.20, 0.30, 0.35, 0.15]),
    )
    node_case(
        "many_impossible_rev",
        np.asarray([0.05, 0.00, 0.00, 0.25, 0.70]),
        np.asarray([0.10, 0.15, 0.20, 0.20, 0.35]),
    )
    random_support_sweep(np.random.default_rng(26062110))
    print(
        "\nRead: when reverse support is missing, the finite-support exponential average "
        "equals reverse support mass, not one. The lost mass lambda is a constraint "
        "on the observation/protocol support, not a small perturbative correction."
    )


if __name__ == "__main__":
    main()
