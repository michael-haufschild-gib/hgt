#!/usr/bin/env python3
"""
R35 STEP 8/9 transfer to Source A/B sigma-orbit balance.

NODE: Parisi q(x) is a full function, not one scalar.
Target: Source A/B classifier is the full orbit-degree profile deg_O(a),
not total divisor degree.

Method #20: name the missing lemma.
"""

from __future__ import annotations

from collections import defaultdict


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        row = [i]
        for j, cb in enumerate(b, start=1):
            row.append(min(prev[j] + 1, row[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = row
    return prev[-1]


def profile(divisor: list[tuple[str, int]]) -> dict[str, int]:
    out: dict[str, int] = defaultdict(int)
    for orbit, coeff in divisor:
        out[orbit] += coeff
    return dict(sorted((k, v) for k, v in out.items() if v))


def classify(divisor: list[tuple[str, int]]) -> str:
    return "CC / Source-B-compatible" if not profile(divisor) else "non-CC / Source-A-type obstruction"


def main() -> None:
    source = "parisi_order_parameter_full_function_not_scalar"
    attempts = [
        "orbit_degree_profile_not_scalar_source_classifier",
        "full_sigma_orbit_balance_function",
        "parisi_qx_for_source_ab_orbit_degrees",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:48s} distance={levenshtein(source, a)}")
    print(f"selected={min(attempts, key=lambda x: levenshtein(source, x))}")

    examples = {
        "constant_multiplier": [],
        "same_orbit_coboundary": [("O_a", +1), ("O_a", -1)],
        "gamma_polynomial_z": [("O_0", +1)],
        "cross_orbit_total_zero": [("O_a", +1), ("O_b", -1)],
        "three_orbit_scalar_zero": [("O_a", +2), ("O_b", -1), ("O_c", -1)],
        "balanced_each_orbit": [("O_a", +2), ("O_a", -2), ("O_b", +1), ("O_b", -1)],
    }
    print("\nSTEP 9 missing lemma: scalar degree zero is not orbit-balance")
    print("example                  total_degree  orbit_profile             classifier")
    for name, div in examples.items():
        total = sum(c for _, c in div)
        prof = profile(div)
        print(f"{name:24s} {total:12d} {str(prof):25s} {classify(div)}")

    print("\nInterpretation")
    print(
        "The transfer lands exactly on the known theorem: the order parameter is the "
        "orbit-degree profile O -> deg_O, not its scalar total. Cross-orbit divisors "
        "can have total degree zero while remaining non-CC."
    )


if __name__ == "__main__":
    main()
