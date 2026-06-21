#!/usr/bin/env python3
"""Low-degree obstruction experiment for the local/global proof-route split.

ResearchNode: M_k/D_2 are local detectors; global proof needs shifted T_k
positivity or faithful kappa_-.

NODE: nonabelian coefficient issues in low degrees.  Abelianized data can vanish
while a noncommutative obstruction remains.

Transfer: finite shifted square-test checks can all pass through order d while
the next shifted Hankel block fails.  The obstruction is stagewise, not closed
by any finite prefix.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import numpy as np


Permutation = tuple[int, int, int]


def compose(p: Permutation, q: Permutation) -> Permutation:
    """Return p after q on {0,1,2}."""

    return tuple(p[i] for i in q)  # type: ignore[return-value]


def inv(p: Permutation) -> Permutation:
    out = [0, 0, 0]
    for i, v in enumerate(p):
        out[v] = i
    return tuple(out)  # type: ignore[return-value]


def parity(p: Permutation) -> int:
    inv_count = 0
    for i in range(3):
        for j in range(i + 1, 3):
            inv_count += p[i] > p[j]
    return inv_count % 2


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        curr = [i]
        for j, cb in enumerate(b, 1):
            curr.append(min(prev[j] + 1, curr[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = curr
    return prev[-1]


def transfer_choice() -> tuple[str, list[tuple[str, int]]]:
    node_test = (
        "Build a nonabelian loop whose abelianized low-degree data vanish, "
        "while the true group-valued obstruction remains nontrivial."
    )
    attempts = {
        "finite_prefix_shifted_hankel": (
            "Build a moment prefix whose shifted low-order square tests pass, "
            "while the next Hankel obstruction remains nontrivial."
        ),
        "window_cover_d2": (
            "Build local windows whose scalar D2 checks pass, while a missing "
            "covering window catches an off-seam atom."
        ),
        "boundary_extension_commutator": (
            "Build two boundary extensions with same bulk scalar data but a "
            "noncommuting extension product that changes inertia."
        ),
    }
    scores = [(name, levenshtein(node_test, text)) for name, text in attempts.items()]
    scores.sort(key=lambda item: item[1])
    return scores[0][0], scores


def hankel(m: list[Fraction], shift: int, d: int) -> np.ndarray:
    return np.array([[float(m[i + j + shift]) for j in range(d + 1)] for i in range(d + 1)])


def inertia(matrix: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int]:
    eig = np.linalg.eigvalsh(matrix)
    return (
        int(np.sum(eig < -tol)),
        int(np.sum(np.abs(eig) <= tol)),
        int(np.sum(eig > tol)),
    )


@dataclass(frozen=True)
class PrefixWitness:
    d: int
    fail_family: str
    moments: list[Fraction]

    def status(self) -> dict[str, object]:
        rows: list[dict[str, object]] = []
        for e in range(self.d + 1):
            rows.append(
                {
                    "order": e,
                    "H0_inertia": inertia(hankel(self.moments, 0, e)),
                    "H1_inertia": inertia(hankel(self.moments, 1, e)),
                }
            )
        next_order = self.d + 1
        return {
            "d": self.d,
            "fail_family": self.fail_family,
            "moments": [str(x) for x in self.moments],
            "passed_through_d": rows,
            "next_H0_inertia": inertia(hankel(self.moments, 0, next_order)),
            "next_H1_inertia": inertia(hankel(self.moments, 1, next_order)),
        }


def h0_next_failure(d: int) -> PrefixWitness:
    # m_0..m_(2d+1) are all 1, so H0/H1 through d are all-ones PSD.
    # m_(2d+2)=0 makes the next H0 block contain [[1,1],[1,0]].
    return PrefixWitness(d=d, fail_family="H0_at_d_plus_1", moments=[Fraction(1)] * (2 * d + 2) + [Fraction(0), Fraction(1)])


def h1_next_failure(d: int) -> PrefixWitness:
    # m_0..m_(2d+2) are all 1, so H0 through d+1 and H1 through d are PSD.
    # m_(2d+3)=0 makes the next H1 block contain [[1,1],[1,0]].
    return PrefixWitness(d=d, fail_family="H1_at_d_plus_1", moments=[Fraction(1)] * (2 * d + 3) + [Fraction(0)])


def main() -> None:
    print("NODE experiment: nonabelian obstruction with trivial abelianized data")
    a: Permutation = (1, 0, 2)  # transposition (01)
    b: Permutation = (0, 2, 1)  # transposition (12)
    comm = compose(compose(compose(a, b), inv(a)), inv(b))
    identity: Permutation = (0, 1, 2)
    print(f"a={a}, b={b}, commutator=[a,b]={comm}")
    print(f"commutator_is_identity: {comm == identity}")
    print(f"abelianized_parity_sum_mod2: {(parity(a)+parity(b)+parity(inv(a))+parity(inv(b))) % 2}")

    chosen, scores = transfer_choice()
    print()
    print("Step 8 transfer attempts by Levenshtein distance")
    for name, score in scores:
        print(f"{name}: {score}")
    print(f"chosen_transfer: {chosen}")

    print()
    print("Transferred shifted-square-test finite-prefix witnesses")
    for d in (1, 2, 4):
        print(h0_next_failure(d).status())
        print(h1_next_failure(d).status())

    print()
    print("Interpretation:")
    print(
        "The NODE falsifies the nearby statement that vanishing abelianized "
        "low-degree data removes the obstruction: the S3 commutator has trivial "
        "parity but is nontrivial. The transferred proof-route statement is the "
        "finite-prefix analogue. For every d, both shifted Hankel families can "
        "pass through order d while the next H0 or H1 block fails. Therefore no "
        "finite batch of shifted square-test checks certifies the global Layer A/B "
        "target; the theorem must remain an all-d statement or provide a genuine "
        "extension theorem with explicit hypotheses."
    )


if __name__ == "__main__":
    main()
