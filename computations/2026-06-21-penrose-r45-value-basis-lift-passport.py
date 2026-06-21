#!/usr/bin/env python3
"""R45 candidate: basis-lift passport for value-axis prime-log corank.

NODE: histone acetylation changes mechanics through charge screening and
reader recruitment.

Transfer: a composite observable can mix two mechanisms.  On the value axis,
relations among composite prime-log features must be lifted back to the
degree-2 monomial basis before being counted as corank evidence.
"""

from __future__ import annotations

import sympy as sp


NODE = "histone acetylation changes mechanics through charge screening and reader recruitment"


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_test() -> None:
    print("NODE two-mechanism acetylation test")
    print("condition acetylation charge reader stiffness viscosity")
    rows = []
    for condition, acetylation, reader_enabled in [
        ("baseline", 0.20, 1.0),
        ("acetylated_reader_on", 0.85, 1.0),
        ("acetylated_reader_blocked", 0.85, 0.0),
    ]:
        charge = 1.15 * acetylation
        reader = reader_enabled * acetylation**2
        stiffness = 1.40 - 0.55 * charge + 0.95 * reader
        viscosity = 0.80 + 0.25 * charge + 1.30 * reader
        rows.append((condition, acetylation, charge, reader, stiffness, viscosity))
        print(
            f"{condition:25s} {acetylation:.2f} {charge:.3f} {reader:.3f} "
            f"{stiffness:.3f} {viscosity:.3f}"
        )
    on = rows[1]
    blocked = rows[2]
    print(
        "same_acetylation_mechanics_gap "
        f"stiffness={abs(on[4] - blocked[4]):.3f} "
        f"viscosity={abs(on[5] - blocked[5]):.3f}"
    )
    print(
        "NODE verdict: the mark is a composite coordinate; charge and reader "
        "mechanisms must be separated before inference."
    )


def feature_coefficients() -> tuple[list[str], sp.Matrix]:
    # Basis is [x^2, xy, y^2], where x=log 2 and y=log 3.
    features = [
        ("x2", (1, 0, 0)),
        ("xy", (0, 1, 0)),
        ("y2", (0, 0, 1)),
        ("log4_sq", (4, 0, 0)),
        ("log6_sq", (1, 2, 1)),
        ("log9_sq", (0, 0, 4)),
        ("log12_sq", (4, 4, 1)),
        ("log18_sq", (1, 4, 4)),
    ]
    names = [name for name, _ in features]
    matrix = sp.Matrix.hstack(*[sp.Matrix(coeff) for _, coeff in features])
    return names, matrix


def relation_to_text(names: list[str], rel: sp.Matrix) -> str:
    pieces = []
    for name, coeff in zip(names, list(rel)):
        if coeff == 0:
            continue
        pieces.append(f"{int(coeff):+d}*{name}")
    return " ".join(pieces) + " = 0"


def transfer_audit() -> None:
    attempts = [
        "prime-log corank needs a composite-feature basis-lift passport",
        "separate charge screening and reader recruitment from log-feature relations",
        "relations among log composites must project nonzero to monomial basis",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(NODE, item)):
        print(f"distance={levenshtein(NODE, text):3d}  {text}")

    print()
    print("STEP9 method #21: build a dependency chain")
    print("1. identify the feature map over Q")
    print("2. quotient construction relations from composite features")
    print("3. only nonzero projected monomial relations count as value-axis corank candidates")
    print("4. then route to prime-log arithmetic, not phase or source geometry")

    names, coeffs = feature_coefficients()
    nullspace = coeffs.nullspace()
    print()
    print("Exact degree-2 basis lift")
    print("basis=[log2^2, log2*log3, log3^2]")
    print(f"feature_count={len(names)} rank={coeffs.rank()} construction_nullity={len(nullspace)}")
    print("feature_names=" + ",".join(names))
    print("first construction relations:")
    for rel in nullspace[:4]:
        print("  " + relation_to_text(names, rel))

    explained = 0
    for rel in nullspace:
        if coeffs * rel == sp.zeros(3, 1):
            explained += 1
    print(f"construction_explained_relations={explained}/{len(nullspace)}")

    composite_names = ["log4_sq", "log6_sq", "log9_sq"]
    composite_cols = [names.index(name) for name in composite_names]
    composite = coeffs[:, composite_cols]
    incomplete_names = ["log6_sq", "log12_sq"]
    incomplete_cols = [names.index(name) for name in incomplete_names]
    incomplete = coeffs[:, incomplete_cols]
    print()
    print("Composite-feature span checks")
    print(
        f"{','.join(composite_names)} rank={composite.rank()} "
        f"det={int(composite.det())}"
    )
    print(f"{','.join(incomplete_names)} rank={incomplete.rank()} det=undefined")

    fake_relation = nullspace[0]
    genuine_candidate = sp.Matrix([3, -5, 2, 0, 0, 0, 0, 0])
    print()
    print("Relation classification examples")
    print(
        "construction_relation_projection="
        + str(list(coeffs * fake_relation))
        + " verdict=quotient"
    )
    print(
        "monomial_candidate_projection="
        + str(list(coeffs * genuine_candidate))
        + " verdict=value-axis arithmetic"
    )
    print(
        "passport_rule=do not count a numerical relation until its exact Q-feature "
        "map has been lifted and construction-nullspace relations have been removed"
    )


def main() -> None:
    print("Penrose R45: value-axis basis-lift passport for prime-log corank")
    print(f"NODE: {NODE}")
    node_test()
    transfer_audit()


if __name__ == "__main__":
    main()
