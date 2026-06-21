#!/usr/bin/env python3
"""Graded versus ungraded positivity for Layer B square tests.

NODE: in supersymmetric quantum mechanics, fermion-number grading is part of
the structure; an ungraded spectrum cannot distinguish paired and unpaired
states.

Transfer: Layer B has two sectorwise shifted square-test forms Q0 and Q1.
This script tests the false shortcut "Q0+Q1 >= 0 should be enough".
"""

from __future__ import annotations

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        curr = [i]
        for j, cb in enumerate(b, 1):
            curr.append(min(prev[j] + 1, curr[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = curr
    return prev[-1]


def witten_index(bosonic: list[int], fermionic: list[int]) -> int:
    return bosonic.count(0) - fermionic.count(0)


def transfer_choice() -> tuple[str, list[tuple[str, int]]]:
    node_test = (
        "Keep ungraded data fixed; compare graded sectors and hidden unpaired "
        "index data."
    )
    attempts = {
        "combined_vs_sector_shifted_forms": (
            "Keep combined data positive; compare graded sectors Q0 Q1 and "
            "hidden negative sector data."
        ),
        "support_only_multiplicity": (
            "Keep support fixed; compare multiplicity weights in moment sums."
        ),
        "finite_prefix_obstruction": (
            "Keep finite prefix fixed; compare next Hankel obstruction stage."
        ),
    }
    scores = [(name, levenshtein(node_test, text)) for name, text in attempts.items()]
    scores.sort(key=lambda item: item[1])
    return scores[0][0], scores


def hankel(m: list[int], shift: int, d: int) -> np.ndarray:
    return np.array([[m[i + j + shift] for j in range(d + 1)] for i in range(d + 1)], dtype=float)


def inertia(matrix: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int]:
    eig = np.linalg.eigvalsh(matrix)
    return (
        int(np.sum(eig < -tol)),
        int(np.sum(np.abs(eig) <= tol)),
        int(np.sum(eig > tol)),
    )


def all_order_witness(max_d: int = 8) -> list[dict[str, object]]:
    even = [1 if n % 2 == 0 else 0 for n in range(2 * max_d + 3)]
    shifted = [0] + even[:-1]
    rows = []
    for name, m in (("even", even), ("shifted_even", shifted)):
        for d in range(1, max_d + 1):
            h0 = hankel(m, 0, d)
            h1 = hankel(m, 1, d)
            rows.append(
                {
                    "witness": name,
                    "d": d,
                    "H0_inertia": inertia(h0),
                    "H1_inertia": inertia(h1),
                    "H0_plus_H1_inertia": inertia(h0 + h1),
                    "combined_is_all_ones": bool(np.allclose(h0 + h1, np.ones_like(h0))),
                }
            )
    return rows


def main() -> None:
    print("NODE experiment: same ungraded spectrum, different Witten index")
    model_a_b = [0, 1, 2]
    model_a_f = [1, 2]
    model_b_b = [1, 2]
    model_b_f = [0, 1, 2]
    print(f"model_A_ungraded={sorted(model_a_b + model_a_f)}")
    print(f"model_B_ungraded={sorted(model_b_b + model_b_f)}")
    print(f"same_ungraded={sorted(model_a_b + model_a_f) == sorted(model_b_b + model_b_f)}")
    print(f"model_A_witten_index={witten_index(model_a_b, model_a_f)}")
    print(f"model_B_witten_index={witten_index(model_b_b, model_b_f)}")

    chosen, scores = transfer_choice()
    print()
    print("Step 8 transfer attempts by Levenshtein distance")
    for name, score in scores:
        print(f"{name}: {score}")
    print(f"chosen_transfer: {chosen}")

    print()
    print("Transferred all-order graded square-test witness")
    for row in all_order_witness():
        print(row)

    print()
    print("Interpretation:")
    print(
        "The NODE shows that ungraded spectral data can be identical while the "
        "graded index changes sign. The shifted square-test transfer has the same "
        "failure mode: for every d tested, the combined form H0+H1 is the all-ones "
        "PSD form while one graded sector is indefinite. Thus the Layer B theorem "
        "cannot be weakened to positivity of Q0+Q1; it must prove sectorwise "
        "positivity of Q0 and Q1."
    )


if __name__ == "__main__":
    main()
