#!/usr/bin/env python3
"""Multiplicity/support invariant experiment for proof-route Layer B.

NODE: inverse spectral theory loses information if multiplicities are collapsed.
Invariant method: hold the distinct support fixed and vary only multiplicities.

Transfer: hold reciprocal support fixed and vary divisor weights in
m_n = sum w_y y^n.  Test whether shifted square-test positivity can change.
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        curr = [i]
        for j, cb in enumerate(b, 1):
            curr.append(min(prev[j] + 1, curr[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = curr
    return prev[-1]


def node_spectral_moments(support: tuple[int, ...], multiplicities: tuple[int, ...], nmax: int) -> list[int]:
    return [sum(m * lam**n for lam, m in zip(support, multiplicities)) for n in range(nmax + 1)]


def complex_pair_moments(pair_weight: int) -> list[Fraction]:
    """Moments for support {1, -1/2+i, -1/2-i}.

    The real atom has weight 2.  Each complex conjugate atom has weight
    pair_weight.  Returned moments are m_0..m_3.
    """

    w0 = Fraction(2)
    # z = -1/2 + i.  Values z^n + conjugate(z)^n for n=0..3.
    pair_power_sums = [
        Fraction(2),
        Fraction(-1),
        Fraction(-3, 2),
        Fraction(11, 4),
    ]
    return [w0 + pair_weight * s for s in pair_power_sums]


def hankel_status(m: list[Fraction]) -> dict[str, object]:
    h0 = np.array([[float(m[0]), float(m[1])], [float(m[1]), float(m[2])]])
    h1 = np.array([[float(m[1]), float(m[2])], [float(m[2]), float(m[3])]])
    eig0 = np.linalg.eigvalsh(h0)
    eig1 = np.linalg.eigvalsh(h1)
    return {
        "moments": [str(x) for x in m],
        "H0": [[str(m[0]), str(m[1])], [str(m[1]), str(m[2])]],
        "H1": [[str(m[1]), str(m[2])], [str(m[2]), str(m[3])]],
        "det_H0": str(m[0] * m[2] - m[1] * m[1]),
        "det_H1": str(m[1] * m[3] - m[2] * m[2]),
        "eig_H0": eig0.tolist(),
        "eig_H1": eig1.tolist(),
        "PSD_pair": bool(eig0[0] >= -1e-12 and eig1[0] >= -1e-12),
    }


def transfer_choice() -> tuple[str, list[tuple[str, int]]]:
    node_test = (
        "Hold distinct eigenvalue support fixed; vary multiplicity; compare "
        "spectral moments and reconstruction constraints."
    )
    attempts = {
        "reciprocal_moment_weights": (
            "Hold distinct reciprocal support fixed; vary divisor multiplicity; "
            "compare shifted Hankel square-test positivity."
        ),
        "projection_rank_kernel": (
            "Hold eigenvalue locations fixed; vary eigenspace projection ranks; "
            "compare kernel feature dimensions."
        ),
        "heat_trace_coefficients": (
            "Hold frequency support fixed; vary heat-trace multiplicities; "
            "compare asymptotic coefficient recovery."
        ),
    }
    scores = [(name, levenshtein(node_test, text)) for name, text in attempts.items()]
    scores.sort(key=lambda item: item[1])
    return scores[0][0], scores


def main() -> None:
    support = (1, 3)
    mult_a = (1, 1)
    mult_b = (2, 1)
    print("NODE invariant: same distinct spectrum, different multiplicities")
    print(f"support: {support}")
    print(f"multiplicities A: {mult_a}")
    print(f"multiplicities B: {mult_b}")
    print(f"spectral moments A: {node_spectral_moments(support, mult_a, 5)}")
    print(f"spectral moments B: {node_spectral_moments(support, mult_b, 5)}")

    chosen, scores = transfer_choice()
    print()
    print("Step 8 transfer attempts by Levenshtein distance")
    for name, score in scores:
        print(f"{name}: {score}")
    print(f"chosen_transfer: {chosen}")

    print()
    print("Transferred invariant: same reciprocal support, different divisor weights")
    print("support: {1, -1/2+i, -1/2-i}; real atom weight fixed at 2")
    for pair_weight in (1, 2):
        print(f"pair_weight={pair_weight}")
        print(hankel_status(complex_pair_moments(pair_weight)))

    print()
    print("Interpretation:")
    print(
        "The distinct support is invariant in both transferred cases, but changing "
        "only the conjugate-pair multiplicity flips the first shifted square-test "
        "status. With pair weight 1, both H0 and H1 are positive definite. With "
        "pair weight 2, both fail. Therefore the proof-route sums must retain the "
        "divisor multiplicities m_rho; support-only reciprocal data are not enough "
        "to certify Layer B positivity."
    )


if __name__ == "__main__":
    main()
