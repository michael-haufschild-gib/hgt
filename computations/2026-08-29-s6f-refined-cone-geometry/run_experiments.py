#!/usr/bin/env python3
"""Exact derivative geometry on computation-free refined S6F cone.

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

# Refined cone proved independently in Lean.
contact.K = sp.Rational(37, 5)
contact.YDSLOPE = sp.Rational(1, 32)


DERIVATIVES = {
    "value": (),
    "dS": ((contact.core.S, 1),),
    "dW": ((contact.W, 1),),
    "dEta": ((contact.ETA, 1),),
    "d2S": ((contact.core.S, 2),),
    "d2W": ((contact.W, 2),),
    "d2Eta": ((contact.ETA, 2),),
    "d3W": ((contact.W, 3),),
    "d3Eta": ((contact.ETA, 3),),
    "dSdW": ((contact.core.S, 1), (contact.W, 1)),
    "dSdEta": ((contact.core.S, 1), (contact.ETA, 1)),
    "dWdEta": ((contact.W, 1), (contact.ETA, 1)),
}


def differentiate(expr, specification):
    answer = expr
    for variable, order in specification:
        answer = sp.diff(answer, variable, order)
    return sp.expand(answer)


def prism_job(name):
    assert contact.PRISM is not None
    return name, contact.half_prism_record(differentiate(contact.PRISM, DERIVATIVES[name]))


def bivariate_face_record(expr, first, second):
    poly = sp.Poly(sp.expand(expr), first, second, domain=sp.QQ)
    values = contact.bivariate_bernstein(poly.as_expr(), first, second)
    return {
        "degrees": [poly.degree(first), poly.degree(second)],
        "terms": len(poly.terms()),
        "ordinary": contact.signs(poly.coeffs()),
        "bernstein": contact.signs(values),
    }


def univariate_bernstein(expr, variable):
    poly = sp.Poly(sp.expand(expr), variable, domain=sp.QQ)
    degree = poly.degree()
    power = [poly.coeff_monomial(variable**i) for i in range(degree + 1)]
    values = [sum(power[i] * sp.binomial(k, i) / sp.binomial(degree, i)
                  for i in range(k + 1)) for k in range(degree + 1)]
    return {
        "degree": degree,
        "terms": len(poly.terms()),
        "ordinary": contact.signs(poly.coeffs()),
        "bernstein": contact.signs(values),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(12, os.cpu_count() or 1))
    args = parser.parse_args()

    print("reconstructing direct D1 on refined cone", file=sys.stderr, flush=True)
    value = contact.normalized_value().subs(contact.core.V, contact.core.Z * contact.core.Y)
    contact.BASE = contact.even_z_to_w(sp.expand(value))
    contact.PRISM = contact.parabolic_prism()
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = dict(pool.map(prism_job, DERIVATIVES))

    prism = contact.PRISM
    upper = sp.expand(prism.subs(contact.ETA, 1))
    lower = sp.expand(prism.subs(contact.ETA, 0))
    upper_unit = sp.expand(upper.subs(contact.W, contact.WMAX * contact.core.T))
    lower_unit = sp.expand(lower.subs(contact.W, contact.WMAX * contact.core.T))
    outer = sp.expand(prism.subs({contact.core.S: 0, contact.W: contact.WMAX}))
    outer_derivative = sp.diff(outer, contact.ETA)
    seam = sp.factor(prism.subs({contact.core.S: 0, contact.W: 0}))

    faces = {
        "upper_value": bivariate_face_record(upper_unit, contact.core.S, contact.core.T),
        "upper_dS": bivariate_face_record(sp.diff(upper_unit, contact.core.S),
                                            contact.core.S, contact.core.T),
        "upper_dW": bivariate_face_record(
            sp.diff(upper, contact.W).subs(contact.W, contact.WMAX * contact.core.T),
            contact.core.S, contact.core.T),
        "upper_d2W": bivariate_face_record(
            -sp.diff(upper, contact.W, 2).subs(contact.W, contact.WMAX * contact.core.T),
            contact.core.S, contact.core.T),
        "lower_value": bivariate_face_record(lower_unit, contact.core.S, contact.core.T),
        "outer_value": univariate_bernstein(outer, contact.ETA),
        "outer_negative_derivative": univariate_bernstein(-outer_derivative, contact.ETA),
    }
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers": args.workers,
        "cone": {
            "X_floor": "191/10 + (37/5) w",
            "y_lower": "13/32 + w/32",
            "y_upper": "33/80 + w/16",
            "w_range": "0 <= w <= 9/100",
        },
        "records": records,
        "faces": faces,
        "seam_independent_of_eta": not seam.has(contact.ETA),
        "seam_sign": "positive" if seam > 0 else "nonpositive",
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
