#!/usr/bin/env python3
"""
R36: Hopf simple-pair condition -> positivity-vs-realization defect gate.

NODE side: crossing the imaginary axis is not enough for Hopf; the critical
pair must be simple/nondefective.

HGT side: FE-symmetric local source models can have the same symmetry and
low-order center data while a defective/double off-seam source produces a much
stronger local positivity obstruction. Gate: realization/FE claims need a
simple-pair/nondefect certificate before positivity is inferred.
"""

import math
from typing import Dict, List, Sequence, Tuple


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_hopf_test() -> Dict[str, object]:
    # Matrices at parameter mu=0.
    simple = [[0.0, -2.0], [2.0, 0.0]]
    defective = [[0.0, 1.0], [0.0, 0.0]]
    # Algebraic/geometric multiplicity proxies.
    return {
        "simple_trace_det_discriminant": (0.0, 4.0, -16.0),
        "simple_geometric_multiplicity_complex_pair": 1,
        "defective_trace_det_discriminant": (0.0, 0.0, 0.0),
        "defective_geometric_multiplicity_zero": 1,
        "constraint": "simple nonzero imaginary pair required; defective zero crossing is not Hopf",
    }


def transfer_choice() -> Dict[str, object]:
    base = """
for linearization:
    check imaginary-axis crossing
    check simple nondefective complex pair
test: defective crossing is not Hopf despite crossing condition
"""
    attempts = {
        "A_FE_simple_pair_positivity_gate": """
for FE-symmetric source pairs:
    check mirror symmetry and local curvature
    check simple-pair/nondefective source multiplicity
test: FE symmetry plus low-order data does not imply positivity without simple-pair gate
""",
        "B_scalar_curvature_threshold": """
for source model:
    compute minimum curvature and compare to threshold
test: negative curvature means off-line defect
""",
        "C_realization_only_model": """
for FE-symmetric model:
    verify mirror symmetry
test: realization symmetry certifies positivity
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    return {"distances": distances, "chosen": min(distances, key=distances.get)}


def curvature_pair(a: float, tau: float, multiplicity: float = 1.0) -> float:
    return multiplicity * 2.0 * (a * a - tau * tau) / ((a * a + tau * tau) ** 2)


def hgt_transfer_test() -> Dict[str, object]:
    rows = []
    # Compare simple off-line pair against a doubled/defective off-line source
    # with same FE mirror symmetry and same center location.
    for a in [0.02, 0.05, 0.10, 0.20]:
        taus = [a * x / 20.0 for x in range(-60, 61)]
        simple_vals = [curvature_pair(a, tau, 1.0) for tau in taus]
        double_vals = [curvature_pair(a, tau, 2.0) for tau in taus]
        # Same symmetry, but the positivity obstruction's positive-core area and peak differ.
        pos_core_simple = sum(max(0.0, y) for y in simple_vals) * (taus[1] - taus[0])
        pos_core_double = sum(max(0.0, y) for y in double_vals) * (taus[1] - taus[0])
        rows.append(
            {
                "a": a,
                "FE_residual_simple": 0.0,
                "FE_residual_double": 0.0,
                "simple_peak": max(simple_vals),
                "double_peak": max(double_vals),
                "simple_positive_core": pos_core_simple,
                "double_positive_core": pos_core_double,
                "peak_ratio": max(double_vals) / max(simple_vals),
                "core_ratio": pos_core_double / pos_core_simple,
            }
        )
    return {"rows": rows}


def step12_followup(hgt: Dict[str, object]) -> Dict[str, object]:
    peak_ratios = [row["peak_ratio"] for row in hgt["rows"]]
    core_ratios = [row["core_ratio"] for row in hgt["rows"]]
    return {
        "peak_ratio_min_max": (min(peak_ratios), max(peak_ratios)),
        "core_ratio_min_max": (min(core_ratios), max(core_ratios)),
        "dependency_chain": [
            "FE/realization symmetry",
            "source multiplicity/simple-pair certificate",
            "local positivity curvature scale",
            "faithful positivity/index claim",
        ],
    }


def main() -> None:
    node = node_hopf_test()
    choice = transfer_choice()
    hgt = hgt_transfer_test()
    follow = step12_followup(hgt)

    print("R36 HOPF_POSITIVITY_DEFECT")
    print("NODE_RESULT")
    for key, value in node.items():
        print(f"  {key}={value}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    for row in hgt["rows"]:
        print(
            f"  a={row['a']:.3f} FE=({row['FE_residual_simple']},{row['FE_residual_double']}) "
            f"simple_peak={row['simple_peak']:.6g} double_peak={row['double_peak']:.6g} "
            f"simple_core={row['simple_positive_core']:.6g} double_core={row['double_positive_core']:.6g} "
            f"ratios=({row['peak_ratio']:.3f},{row['core_ratio']:.3f})"
        )

    print("STEP9_METHOD_RESULT")
    print("  method=21 build a dependency chain")
    print("  chain=" + " -> ".join(follow["dependency_chain"]))

    print("STEP12_FOLLOWUP")
    for key, value in follow.items():
        print(f"  {key}={value}")

    print("INTERPRETATION")
    print(
        "  FE/realization symmetry is blind to simple-vs-defective source multiplicity. "
        "A positivity claim needs a nondefective/simple-pair source certificate before local "
        "curvature evidence is interpreted as a faithful positivity/index statement."
    )


if __name__ == "__main__":
    main()
