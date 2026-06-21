#!/usr/bin/env python3
"""NODE representation test: atypical periodic invariant measures.

Expected outcome: likely dead end, since the proof-route transfer is the
known finite-prefix/truncated-moment ambiguity.
"""

from __future__ import annotations

import numpy as np


def logistic_orbit(x: float, r: float = 4.0, steps: int = 2000, burn: int = 500) -> np.ndarray:
    vals = []
    for i in range(steps + burn):
        x = r * x * (1.0 - x)
        if i >= burn:
            vals.append(x)
    return np.array(vals)


def moments(xs: np.ndarray, max_k: int) -> list[float]:
    return [float(np.mean(xs**k)) for k in range(max_k + 1)]


def hankel(m: list[float], shift: int, d: int) -> np.ndarray:
    return np.array([[m[i + j + shift] for j in range(d + 1)] for i in range(d + 1)])


def inertia(M: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int]:
    e = np.linalg.eigvalsh(M)
    return (int(np.sum(e < -tol)), int(np.sum(abs(e) <= tol)), int(np.sum(e > tol)))


def main() -> None:
    print("NODE representation: chaotic physical sample versus periodic invariant measure")
    chaotic = logistic_orbit(0.123456)
    # Fixed point x=3/4 is a valid invariant measure for r=4 but atypical for Lebesgue-a.e. starts.
    periodic = np.full_like(chaotic, 0.75)
    for name, xs in (("physical_sample", chaotic), ("fixed_orbit_measure", periodic)):
        m = moments(xs, 6)
        print(
            {
                "name": name,
                "moments_0_to_6": [round(v, 8) for v in m],
                "H0_d2_inertia": inertia(hankel(m, 0, 2)),
                "H1_d2_inertia": inertia(hankel(m, 1, 2)),
            }
        )

    print()
    print("Proof-route transfer audit:")
    print(
        "Both physical and atypical finite/atomic invariant measures give PSD "
        "truncated Hankel forms. This only says finite square-test positivity can "
        "be represented by finite atomic impostors. That is the existing "
        "finite-prefix/finite-flat warning, not a new proof-route result."
    )


if __name__ == "__main__":
    main()
