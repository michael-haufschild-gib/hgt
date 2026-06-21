#!/usr/bin/env python3
"""
Attempt 9 transfer experiment.

ResearchNode: Faithful index, not measured density.
NODE constraint: same absolute defect density can have different signed channels.

Transfer:
  Compare quadratic forms with the same scalar density summaries but different
  Sylvester negative index.  The faithful quantity is inertia, not trace-like
  measured density.
"""

from __future__ import annotations

import numpy as np


def inertia(eigs: np.ndarray, tol: float = 1e-12) -> tuple[int, int, int]:
    return (
        int(np.sum(eigs < -tol)),
        int(np.sum(np.abs(eigs) <= tol)),
        int(np.sum(eigs > tol)),
    )


def summaries(eigs: np.ndarray) -> dict[str, float | tuple[int, int, int]]:
    return {
        "sum_abs": float(np.sum(np.abs(eigs))),
        "frob": float(np.linalg.norm(eigs)),
        "max_abs": float(np.max(np.abs(eigs))),
        "trace": float(np.sum(eigs)),
        "inertia": inertia(eigs),
    }


def print_case(name: str, eigs: list[float]) -> None:
    arr = np.array(eigs, dtype=float)
    s = summaries(arr)
    print(name)
    print(f"  eigs={arr}")
    print(
        f"  measured: sum_abs={s['sum_abs']:.3f}, frob={s['frob']:.3f}, "
        f"max_abs={s['max_abs']:.3f}, trace={s['trace']:.3f}"
    )
    print(f"  faithful inertia (neg,zero,pos)={s['inertia']}")
    print()


def main() -> None:
    print("SCALAR DENSITY VS FAITHFUL INDEX")
    print()
    print_case("all-positive reference", [1, 1, 1, 1])
    print_case("one signed defect, same absolute spectrum", [-1, 1, 1, 1])
    print_case("two signed defects, same absolute spectrum", [-1, -1, 1, 1])
    print("same absolute eigenvalue density and Frobenius norm do not determine the negative index.")
    print()
    print("reverse check: same faithful index can have different scalar densities")
    print_case("one negative, small scale", [-0.1, 0.2, 0.2, 0.2])
    print_case("one negative, large scale", [-10.0, 0.2, 0.2, 0.2])


if __name__ == "__main__":
    main()
