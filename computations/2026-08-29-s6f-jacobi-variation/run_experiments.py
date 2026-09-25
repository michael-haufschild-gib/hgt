#!/usr/bin/env python3
"""Exact Jacobi/Loewner hostile test for refined-cone D1 scale increase.

Diagnostic only. No output may be imported into Lean proofs.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
import os
import sys
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
CONTACT_PATH = HERE.parent / "2026-08-29-s6f-parabolic-d1-contact" / "run_experiments.py"
spec = importlib.util.spec_from_file_location("contact", CONTACT_PATH)
contact = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = contact
spec.loader.exec_module(contact)

# Sharpened cone proved independently, without numerical input.
contact.K = sp.Rational(37, 5)
contact.YDSLOPE = sp.Rational(1, 32)

EXPRESSIONS: dict[str, sp.Expr] = {}


def cov_lie(expr: sp.Expr) -> sp.Expr:
    return sp.expand(contact.core.lie3(expr) + sp.Rational(1, 2) * contact.core.B * expr)


def signed_reflected_jets() -> list[sp.Expr]:
    f = [contact.core.Q]
    for _ in range(8):
        f.append(cov_lie(f[-1]))
    return [
        sp.expand(f[0] ** 2),
        sp.expand(2 * (f[0] * f[2] - f[1] ** 2)),
        sp.expand(2 * f[0] * f[4] - 8 * f[1] * f[3] + 6 * f[2] ** 2),
        sp.expand(2 * f[0] * f[6] - 12 * f[1] * f[5] +
                  30 * f[2] * f[4] - 20 * f[3] ** 2),
        sp.expand(2 * f[0] * f[8] - 16 * f[1] * f[7] +
                  56 * f[2] * f[6] - 112 * f[3] * f[5] + 70 * f[4] ** 2),
    ]


def normalized_component(expr: sp.Expr) -> sp.Expr:
    qexpr = (contact.core.R**2 * (1 - contact.core.Z**2 +
             sp.Rational(2, 3) * (contact.core.Z - contact.core.V) ** 2) - 6) / 16
    transformed = expr.subs({
        contact.core.U: contact.core.R * contact.core.V,
        contact.core.B: contact.core.R * (contact.core.Z - contact.core.V) / 3,
        contact.core.Q: qexpr,
    })
    scaled = contact.eliminate_even_scale(sp.expand(transformed))
    triangle = scaled.subs(contact.core.V, contact.core.Z * contact.core.Y)
    return contact.even_z_to_w(sp.expand(triangle))


def refined_prism(expr: sp.Expr) -> sp.Expr:
    y = (contact.YL0 + contact.YLSLOPE * contact.W +
         contact.ETA * (contact.YD0 + contact.YDSLOPE * contact.W))
    return sp.expand(expr.subs({
        contact.core.X: contact.X0 + contact.K * contact.W + contact.core.S,
        contact.core.Y: y,
    }))


def principal_minors_through_two(matrix: sp.Matrix, prefix: str) -> dict[str, sp.Expr]:
    answer: dict[str, sp.Expr] = {}
    for i in range(3):
        answer[f"{prefix}_diag_{i}"] = sp.expand(matrix[i, i])
    for i, j in ((0, 1), (0, 2), (1, 2)):
        answer[f"{prefix}_minor_{i}{j}"] = sp.expand(
            matrix.extract((i, j), (i, j)).det())
    return answer


def record_job(name: str) -> tuple[str, dict]:
    return name, contact.half_prism_record(EXPRESSIONS[name])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(14, os.cpu_count() or 1))
    parser.add_argument("--determinant-only", action="store_true")
    parser.add_argument("--determinant-face", choices=("seam", "outer"))
    args = parser.parse_args()

    print("reconstructing signed reflected-jet matrix", file=sys.stderr, flush=True)
    p0, p2, p4, p6, p8 = [normalized_component(p) for p in signed_reflected_jets()]
    intrinsic_hankel = sp.Matrix(((p0, p2, p4), (p2, p4, p6), (p4, p6, p8)))
    intrinsic_scale_velocity = intrinsic_hankel.diff(contact.core.X)
    scale_velocity = intrinsic_scale_velocity.applyfunc(refined_prism)

    global EXPRESSIONS
    if args.determinant_only or args.determinant_face:
        a, b, c = (intrinsic_scale_velocity[0, 0], intrinsic_scale_velocity[0, 1],
                   intrinsic_scale_velocity[0, 2])
        d, e, f = (intrinsic_scale_velocity[1, 1], intrinsic_scale_velocity[1, 2],
                   intrinsic_scale_velocity[2, 2])
        determinant = refined_prism(sp.expand(
            a * d * f + 2 * b * c * e - a * e**2 - d * c**2 - f * b**2))
        if args.determinant_face == "seam":
            determinant = determinant.subs({contact.W: 0, contact.ETA: 0})
        elif args.determinant_face == "outer":
            determinant = determinant.subs({contact.W: contact.WMAX, contact.core.S: 0})
        EXPRESSIONS = {
            "dH_det": sp.expand(determinant)
        }
        print(f"testing rank-three Loewner determinant face={args.determinant_face}",
              file=sys.stderr, flush=True)
    else:
        EXPRESSIONS = principal_minors_through_two(scale_velocity, "dH")
        print("testing diagonal and rank-two Loewner minors", file=sys.stderr, flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = dict(pool.map(record_job, sorted(EXPRESSIONS)))

    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "question": "does H' >= 0 explain scale increase of det(H)?",
        "cone": {
            "X_floor": "191/10 + (37/5) w",
            "y_lower": "13/32 + w/32",
            "y_upper": "33/80 + w/16",
            "w_range": "0 <= w <= 9/100",
        },
        "workers": args.workers,
        "records": records,
        "loewner_rank_two_necessary_conditions_survive": all(
            record["bernstein"]["negative"] == 0
            for record in records.values()),
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
