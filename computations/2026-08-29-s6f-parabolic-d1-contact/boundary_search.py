#!/usr/bin/env python3
"""Locate exact boundary geometry of the parabolic D1 certificate.

Diagnostic only. No output is admissible in a Lean proof. The exact sign
certificate already reduces scale to zero slack and clock-square to its two
endpoints if scale monotonicity and clock concavity are proved. This script
asks where the remaining one-variable wall interpolation attains its minima.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "run_experiments.py"
spec = importlib.util.spec_from_file_location("contact", SCRIPT)
contact = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = contact
spec.loader.exec_module(contact)


def sign(value: sp.Expr) -> str:
    return "positive" if value > 0 else "negative" if value < 0 else "zero"


def face_record(expr: sp.Expr) -> dict:
    poly = sp.Poly(sp.factor(expr), contact.ETA, domain=sp.QQ)
    derivative = poly.diff()
    roots = sp.nroots(derivative, n=60, maxsteps=500)
    real_roots = sorted(float(sp.re(root)) for root in roots
                        if abs(float(sp.im(root))) < 1e-40 and 0 < float(sp.re(root)) < 1)
    candidates = [(0.0, float(sp.N(poly.eval(0), 30))),
                  (1.0, float(sp.N(poly.eval(1), 30)))]
    for root in real_roots:
        candidates.append((root, float(sp.N(poly.eval(sp.Float(root, 60)), 30))))
    candidates.sort(key=lambda item: item[1])
    coefficient, factors = sp.factor_list(poly.as_expr())
    return {
        "degree": poly.degree(),
        "terms": len(poly.terms()),
        "factor_coefficient": str(coefficient),
        "factor_degrees": [[sp.Poly(f, contact.ETA).degree(), power] for f, power in factors],
        "critical_root_count_exact": int(sp.count_roots(derivative.as_expr(), 0, 1)),
        "critical_roots_numeric": [format(root, ".16g") for root in real_roots],
        "candidate_values_ascending": [
            {"eta": format(eta, ".16g"), "value": format(value, ".16g")}
            for eta, value in candidates
        ],
        "endpoint_derivative_signs": {
            "eta_0": sign(derivative.eval(0)),
            "eta_1": sign(derivative.eval(1)),
        },
    }


def main() -> None:
    print("reconstructing parabolic D1 prism", file=sys.stderr, flush=True)
    value = contact.normalized_value().subs(contact.core.V, contact.core.Z * contact.core.Y)
    contact.BASE = contact.even_z_to_w(sp.expand(value))
    contact.PRISM = contact.parabolic_prism()
    base = contact.PRISM.subs(contact.core.S, 0)

    seam = sp.factor(base.subs(contact.W, 0))
    outer = sp.factor(base.subs(contact.W, contact.WMAX))
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "seam_independent_of_eta": not seam.has(contact.ETA),
        "seam_sign": sign(seam),
        "outer": face_record(outer),
    }
    Path("boundary-results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
