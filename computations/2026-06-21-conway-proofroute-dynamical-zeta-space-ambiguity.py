#!/usr/bin/env python3
"""
Workflow NODE: in dynamical zeta functions, the same formal orbit data can
lead to different analytic objects when the transfer-operator completion adds
or removes spectrum.

Proof-route stress test: can the analogous "same finite moment prefix, hidden
extra spectrum" produce a new route to the reciprocal seam Stieltjes wall?

Verdict target: finite prefixes can be made nearly indistinguishable while a
non-real conjugate atom is present. That is only the already-known all-order
Hankel/no-margin warning unless a new all-order certificate appears.
"""

from __future__ import annotations

import cmath
import math

import numpy as np


def moments(atoms: list[complex], weights: list[float], max_k: int) -> np.ndarray:
    return np.array(
        [sum(w * (a**k) for a, w in zip(atoms, weights)) for k in range(max_k + 1)],
        dtype=np.complex128,
    )


def hankel_min_eigs(m: np.ndarray, max_d: int) -> list[float]:
    out: list[float] = []
    for d in range(1, max_d + 1):
        h = np.array([[m[i + j] for j in range(d + 1)] for i in range(d + 1)], dtype=np.complex128)
        # The conjugate-pair perturbation makes the moments real up to roundoff.
        out.append(float(np.linalg.eigvalsh(h.real).min()))
    return out


def first_failure(m: np.ndarray, max_d: int, tol: float = -1e-13) -> int | None:
    for d, val in enumerate(hankel_min_eigs(m, max_d), start=1):
        if val < tol:
            return d
    return None


def main() -> None:
    # A toy positive Stieltjes background, standing in for the on-seam atoms.
    base_atoms = [0.50, 0.23, 0.09, 0.035, 0.012]
    base_weights = [1.0, 0.8, 0.55, 0.35, 0.2]

    # A hidden off-real conjugate pair, standing in for an off-seam reciprocal atom pair.
    # Small weight makes low moments nearly indistinguishable; nonzero angle makes it
    # impossible to be a positive measure on [0, infinity) in the all-order limit.
    eps = 2.0e-9
    radius = 0.72
    theta = 0.85
    off_atoms = [radius * cmath.exp(1j * theta), radius * cmath.exp(-1j * theta)]
    off_weights = [eps, eps]

    max_k = 120
    max_d = 50
    m_base = moments([complex(x) for x in base_atoms], base_weights, max_k)
    m_hidden = moments([complex(x) for x in base_atoms] + off_atoms, base_weights + off_weights, max_k)

    prefix = 16
    rel = np.max(np.abs(m_hidden[: prefix + 1] - m_base[: prefix + 1])) / np.max(np.abs(m_base[: prefix + 1]))
    failure = first_failure(m_hidden, max_d)

    print("=== finite-prefix ambiguity stress test ===")
    print(f"base atoms: {base_atoms}")
    print(f"hidden conjugate atom: radius={radius}, theta={theta}, eps={eps}")
    print(f"max relative change in moments k<= {prefix}: {rel:.3e}")
    print(f"first negative leading Hankel min eigenvalue through d={max_d}: {failure}")
    for d in [2, 4, 8, 12, 16, 24, 32, 40, 50]:
        val = hankel_min_eigs(m_hidden, d)[-1]
        print(f"d={d:02d} min_eig={val:+.6e}")

    print()
    print("interpretation:")
    print("- Finite prefixes can be numerically identical while hidden non-real atoms exist.")
    print("- The first useful statement is therefore all-order Hankel/Stieltjes, not a finite detector.")
    print("- This reproduces the proof-route no-margin warning; no new proof-route theorem is produced.")


if __name__ == "__main__":
    main()
