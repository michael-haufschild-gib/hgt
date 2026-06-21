#!/usr/bin/env python3
"""Dependency-chain experiment: nullity is not negative index.

NODE: the zero Neumann eigenvalue has multiplicity equal to connected
components.  Nullity can be boundary/topology data, not instability.

Transfer: Layer C must use the negative inertia `neg(Q_xi)`, not determinant
sign, nonzero gap, or positive definiteness.  PSD with kernel is compatible
with zero negative index.
"""

from __future__ import annotations

import numpy as np


def inertia(vals: list[float], tol: float = 1e-10) -> tuple[int, int, int]:
    arr = np.array(vals)
    return (
        int(np.sum(arr < -tol)),
        int(np.sum(np.abs(arr) <= tol)),
        int(np.sum(arr > tol)),
    )


def summary(name: str, vals: list[float]) -> dict[str, object]:
    return {
        "name": name,
        "eigenvalues": vals,
        "inertia_neg_zero_pos": inertia(vals),
        "determinant": float(np.prod(vals)),
        "min_eigenvalue": min(vals),
    }


def neumann_path_eigs(components: int, modes_per_component: int = 5) -> list[float]:
    vals = []
    for _ in range(components):
        vals.extend([float(k * k) for k in range(modes_per_component)])
    return sorted(vals)


def main() -> None:
    print("NODE dependency chain: Neumann zero modes count components")
    for c in (1, 2, 3):
        vals = neumann_path_eigs(c)
        print(summary(f"{c}_components_neumann", vals))

    print()
    print("Layer C transfer: determinant/gap/PD are not faithful substitutes for negative index")
    examples = [
        ("psd_with_kernel_no_offline", [0.0, 1.0, 2.0]),
        ("one_negative_with_kernel", [-1.0, 0.0, 2.0]),
        ("det_positive_neg0", [1.0, 2.0, 3.0, 4.0]),
        ("det_positive_neg2", [-1.0, -2.0, 3.0, 4.0]),
    ]
    for name, vals in examples:
        print(summary(name, vals))

    print()
    print("Interpretation:")
    print(
        "The NODE chain separates nullity from instability: more Neumann "
        "components add zero modes but no negative modes. The Layer C transfer "
        "is the same dependency chain. A faithful RH index must be the negative "
        "inertia itself, optionally after a specified kernel quotient. Determinant "
        "zero, determinant sign, min eigenvalue equal to zero, or failure of "
        "positive definiteness are not faithful substitutes for off-line-pair count."
    )


if __name__ == "__main__":
    main()
