#!/usr/bin/env python3
"""Attack-as-false toy for explicit-formula component positivity.

NODE: diffractive/boundary corrections in trace formulas are missed if one
keeps only bulk periodic-orbit contributions.

Expected proof-route outcome: dead end if it only says componentwise arch/prime
or bulk/boundary positivity is not available.
"""

from __future__ import annotations

import numpy as np


def inertia(M: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int]:
    e = np.linalg.eigvalsh(M)
    return (int(np.sum(e < -tol)), int(np.sum(abs(e) <= tol)), int(np.sum(e > tol)))


def main() -> None:
    # Completed residue is PSD, but neither component has to be PSD.
    completed = np.eye(2)
    bulk = np.array([[2.0, 3.0], [3.0, 2.0]])
    correction = completed - bulk
    print("NODE transfer toy: completed positivity is not componentwise positivity")
    print({"bulk": bulk.tolist(), "inertia": inertia(bulk)})
    print({"correction": correction.tolist(), "inertia": inertia(correction)})
    print({"completed": completed.tolist(), "inertia": inertia(completed)})
    print()
    print(
        "Interpretation: missing trace-formula corrections can change the "
        "quadratic form, but this only restates the known seam-blocked split: "
        "the proof route must prove positivity of the completed residue, not "
        "componentwise positivity of bulk/prime/Gamma pieces."
    )


if __name__ == "__main__":
    main()
