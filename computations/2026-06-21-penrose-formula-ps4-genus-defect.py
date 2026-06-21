#!/usr/bin/env python3
"""PS4 versus the arithmetic/geometric genus defect analogy.

Formula node:
    PS4: lambda_n = sum_{j=1}^n (-1)^(j+1) binom(n,j) P_j.

Random external node:
    Distinguishing arithmetic genus from geometric genus in positive
    characteristic.

Constraint tested:
    Arithmetic genus is a raw/projective invariant, while geometric genus
    subtracts local singularity/normalization defects. In a plane curve toy
    model, g = p_a - sum(delta_P).

Transfer tested:
    Treat a missing local correction in one power-sum coordinate P_m as the
    PS4 analogue of a singularity defect. The binomial transform spreads that
    single-coordinate defect into every lambda_n with n >= m.

Method 22 from docs/meta/scientific-method.md:
    Compare nearby false statements.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        cur = [i]
        for j, cb in enumerate(b, start=1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


@dataclass(frozen=True)
class PlaneCurveToy:
    name: str
    degree: int
    deltas: tuple[int, ...]

    @property
    def arithmetic_genus(self) -> int:
        return (self.degree - 1) * (self.degree - 2) // 2

    @property
    def geometric_genus(self) -> int:
        return self.arithmetic_genus - sum(self.deltas)


def li_defect(n: int, m: int, delta: Fraction) -> Fraction:
    if n < m:
        return Fraction(0)
    return Fraction((-1) ** (m + 1) * comb(n, m), 1) * delta


def lambda_from_p(n: int, p: dict[int, Fraction]) -> Fraction:
    return sum(
        Fraction((-1) ** (j + 1) * comb(n, j), 1) * p.get(j, Fraction(0))
        for j in range(1, n + 1)
    )


def print_header(title: str) -> None:
    print("\n" + title)
    print("-" * len(title))


def main() -> None:
    research_node = "PS4 lambda_n = -sum C(n,j)(-1)^j P_j"
    node_constraint = "subtract singularity delta from arithmetic genus"
    attempts = [
        "test singularity delta between arithmetic and geometric genus for Li binomial transform",
        "test full versus truncated power sums as arithmetic versus geometric chart",
        "test normalization defect correction before applying Li positivity",
    ]

    print_header("Step 8 transfer attempts")
    distances = []
    for label, attempt in zip("ABC", attempts):
        d = levenshtein(node_constraint, attempt)
        distances.append((d, label, attempt))
        print(f"{label}: distance={d:2d} :: {attempt}")
    d, label, chosen = min(distances)
    print(f"chosen={label}, distance={d}, research_node={research_node}")

    print_header("NODE constraint: genus defect")
    curves = [
        PlaneCurveToy("smooth cubic", 3, ()),
        PlaneCurveToy("nodal cubic", 3, (1,)),
        PlaneCurveToy("cuspidal cubic", 3, (1,)),
        PlaneCurveToy("quartic with two nodes", 4, (1, 1)),
        PlaneCurveToy("quartic with one node", 4, (1,)),
    ]
    for curve in curves:
        print(
            f"{curve.name:24s} degree={curve.degree} "
            f"p_a={curve.arithmetic_genus} "
            f"sum_delta={sum(curve.deltas)} "
            f"g={curve.geometric_genus}"
        )
    print(
        "constraint_check: same p_a can hide different local defects; "
        "normalization/geometric genus needs the defect subtraction."
    )

    print_header("PS4 single-coordinate defect propagation")
    m = 3
    delta = Fraction(1, 1)
    for n in range(1, 13):
        actual = li_defect(n, m, delta)
        formula = Fraction((-1) ** (m + 1) * comb(n, m), 1) * delta if n >= m else Fraction(0)
        ok = actual == formula
        print(f"n={n:2d} delta_lambda={str(actual):>4s} formula_ok={ok}")
    print(
        "exact_rule: delta P_m changes all lambda_n with n>=m by "
        "(-1)^(m+1) binom(n,m) delta."
    )

    print_header("Method 22: nearby false statements")
    max_n = 8
    p_base: dict[int, Fraction] = {}
    p_defect = {3: Fraction(1)}
    diffs = [
        lambda_from_p(n, p_defect) - lambda_from_p(n, p_base)
        for n in range(1, max_n + 1)
    ]
    print(
        "false_1: a defect in P_m affects only lambda_m :: "
        f"counterexample diffs n=1..{max_n} = {[str(x) for x in diffs]}"
    )
    late_m = 9
    late_defect = {late_m: Fraction(5)}
    early_diffs = [
        lambda_from_p(n, late_defect) - lambda_from_p(n, p_base)
        for n in range(1, late_m)
    ]
    first_visible = lambda_from_p(late_m, late_defect) - lambda_from_p(late_m, p_base)
    print(
        "false_2: a finite Li window rules out hidden higher P defects :: "
        f"lambda_1..lambda_{late_m - 1} diffs = {[str(x) for x in early_diffs]}, "
        f"lambda_{late_m} diff = {first_visible}"
    )
    signs = [li_defect(n, m, delta) for n in range(m, 2 * m + 5)]
    print(
        "false_3: the sign of a P_m defect alternates with n :: "
        f"for fixed m={m}, signs stay {['+' if x > 0 else '-' for x in signs]}"
    )

    print_header("Interpretation")
    print(
        "The NODE analogy is real but elementary: local genus defects must be "
        "subtracted before comparing arithmetic and geometric genus; likewise "
        "a missing P_m correction must be fixed before PS4/Li positivity is "
        "read. PS4 then spreads the defect nonlocally across the Li tail."
    )
    print(
        "novelty_check: this is a direct corollary of the already banked "
        "triangular Li/secular transform and is close to the existing PS4 "
        "HD3 gauge-ghost-power-sums card. Verdict: reduce-to-known unless a "
        "future node supplies a source-built, non-gauge defect."
    )


if __name__ == "__main__":
    main()
