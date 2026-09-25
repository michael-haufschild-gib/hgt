#!/usr/bin/env python3
"""Exact hostile test of direct rank-three D1 positivity on the formal parabolic cone.

Diagnostic only. No output is admissible in a Lean proof.

The computation-free cone is

    X >= 191/10 + (147/20) w,
    13/32 + w/32 <= y <= 33/80 + w/12,
    0 <= w <= 9/100.

This script asks whether the D1 polynomial itself, rather than its projective
drift, has a direct half-prism Bernstein certificate. It also tests the three
coordinate directions that would reduce a failed direct certificate to a
rank-two boundary-contact problem.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
CORE_PATH = HERE.parent / "2026-08-29-s6f-normalized-chamber-search" / "run_experiments.py"
spec = importlib.util.spec_from_file_location("s6f_core", CORE_PATH)
core = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = core
spec.loader.exec_module(core)

W = sp.Symbol("w")
ETA = sp.Symbol("eta")
X0 = sp.Rational(191, 10)
K = sp.Rational(147, 20)
WMAX = sp.Rational(9, 100)
YL0 = sp.Rational(13, 32)
YD0 = sp.Rational(1, 160)
YLSLOPE = sp.Rational(1, 32)
YDSLOPE = sp.Rational(5, 96)
BASE: sp.Expr | None = None
PRISM: sp.Expr | None = None


def source_positive_value() -> sp.Expr:
    def cov_lie(expr: sp.Expr) -> sp.Expr:
        return sp.expand(core.lie3(expr) + sp.Rational(1, 2) * core.B * expr)

    jets = [core.Q]
    for _ in range(8):
        jets.append(cov_lie(jets[-1]))
    p0 = jets[0] ** 2
    p2 = 2 * (jets[0] * jets[2] - jets[1] ** 2)
    p4 = 2 * jets[0] * jets[4] - 8 * jets[1] * jets[3] + 6 * jets[2] ** 2
    p6 = 2 * jets[0] * jets[6] - 12 * jets[1] * jets[5] + 30 * jets[2] * jets[4] - 20 * jets[3] ** 2
    p8 = (2 * jets[0] * jets[8] - 16 * jets[1] * jets[7] +
          56 * jets[2] * jets[6] - 112 * jets[3] * jets[5] + 70 * jets[4] ** 2)
    return sp.expand(p0 * p4 * p8 - p0 * p6**2 - p2**2 * p8 +
                     2 * p2 * p4 * p6 - p4**3)


def eliminate_even_scale(expr: sp.Expr) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), core.R, core.V, core.Z, domain=sp.QQ)
    out = sp.Rational(0)
    odd = []
    for (er, ev, ez), coeff in poly.terms():
        if er % 2:
            odd.append((er, ev, ez))
        out += coeff * core.X ** (er // 2) * core.V**ev * core.Z**ez
    assert not odd, f"unexpected odd scale powers: {odd[:8]}"
    return sp.expand(out)


def normalized_value() -> sp.Expr:
    qexpr = (core.R**2 * (1 - core.Z**2 +
             sp.Rational(2, 3) * (core.Z - core.V) ** 2) - 6) / 16
    transformed = source_positive_value().subs({
        core.U: core.R * core.V,
        core.B: core.R * (core.Z - core.V) / 3,
        core.Q: qexpr,
    })
    return eliminate_even_scale(sp.expand(transformed))


def even_z_to_w(expr: sp.Expr) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), core.X, core.Z, core.Y, domain=sp.QQ)
    out = sp.Rational(0)
    odd = []
    for (ex, ez, ey), coeff in poly.terms():
        if ez % 2:
            odd.append((ex, ez, ey))
        out += coeff * core.X**ex * W ** (ez // 2) * core.Y**ey
    assert not odd, f"unexpected odd z powers: {odd[:8]}"
    return sp.expand(out)


def signs(values: list[sp.Rational]) -> dict:
    return {
        "count": len(values),
        "negative": sum(bool(v < 0) for v in values),
        "zero": sum(bool(v == 0) for v in values),
        "positive": sum(bool(v > 0) for v in values),
        "minimum": str(min(values)),
        "maximum": str(max(values)),
    }


def bivariate_bernstein(expr: sp.Expr, a: sp.Symbol, b: sp.Symbol) -> list[sp.Rational]:
    poly = sp.Poly(expr, a, b, domain=sp.QQ)
    da, db = poly.degree(a), poly.degree(b)
    power = {(i, j): poly.coeff_monomial(a**i * b**j)
             for i in range(da + 1) for j in range(db + 1)}
    return [
        sum(power[i, j] * sp.binomial(ka, i) / sp.binomial(da, i) *
            sp.binomial(kb, j) / sp.binomial(db, j)
            for i in range(ka + 1) for j in range(kb + 1))
        for ka in range(da + 1) for kb in range(db + 1)
    ]


def half_prism_record(expr: sp.Expr) -> dict:
    unit = sp.expand(expr.subs(W, WMAX * core.T))
    poly = sp.Poly(unit, core.S, core.T, ETA, domain=sp.QQ)
    by_s: dict[int, sp.Expr] = {}
    for (es, et, ee), coeff in poly.terms():
        by_s[es] = by_s.get(es, sp.Rational(0)) + coeff * core.T**et * ETA**ee
    bernstein: list[sp.Rational] = []
    for es in sorted(by_s):
        bernstein.extend(bivariate_bernstein(by_s[es], core.T, ETA))
    digest = hashlib.sha256("\n".join(str(v) for v in bernstein).encode("ascii")).hexdigest()
    return {
        "degrees": [poly.degree(core.S), poly.degree(core.T), poly.degree(ETA)],
        "terms": len(poly.terms()),
        "ordinary": signs(poly.coeffs()),
        "bernstein": signs(bernstein),
        "bernstein_sha256": digest,
    }


def parabolic_prism() -> sp.Expr:
    assert BASE is not None
    y = YL0 + YLSLOPE * W + ETA * (YD0 + YDSLOPE * W)
    return sp.expand(BASE.subs({core.X: X0 + K * W + core.S, core.Y: y}))


def record_job(kind: str) -> tuple[str, dict]:
    assert PRISM is not None
    value = PRISM
    if kind == "value":
        expr = value
    elif kind == "dS":
        expr = sp.diff(value, core.S)
    elif kind == "dW":
        expr = sp.diff(value, W)
    elif kind == "dEta":
        expr = sp.diff(value, ETA)
    elif kind == "d2W":
        expr = sp.diff(value, W, 2)
    elif kind == "d2Eta":
        expr = sp.diff(value, ETA, 2)
    elif kind == "d2S":
        expr = sp.diff(value, core.S, 2)
    elif kind == "d3W":
        expr = sp.diff(value, W, 3)
    elif kind == "d3Eta":
        expr = sp.diff(value, ETA, 3)
    else:
        raise ValueError(kind)
    return kind, half_prism_record(expr)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(5, os.cpu_count() or 1))
    args = parser.parse_args()

    print("reconstructing source-positive D1", file=sys.stderr, flush=True)
    value = normalized_value().subs(core.V, core.Z * core.Y)
    global BASE, PRISM
    BASE = even_z_to_w(sp.expand(value))
    PRISM = parabolic_prism()
    print("dispatching direct cone and directional tests", file=sys.stderr, flush=True)
    kinds = ["value", "dS", "dW", "dEta", "d2W", "d2Eta", "d2S", "d3W", "d3Eta"]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = dict(pool.map(record_job, kinds))

    prism = PRISM
    corners = {}
    for eta in (0, 1):
        for w_name, w_value in (("seam", 0), ("outer", WMAX)):
            corners[f"{w_name}_eta_{eta}"] = str(sp.factor(prism.subs({
                core.S: 0, W: w_value, ETA: eta})))
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers": args.workers,
        "cone": {
            "X_floor": "191/10 + (147/20) w",
            "y_lower": "13/32 + w/32",
            "y_upper": "33/80 + w/12",
            "w_range": "0 <= w <= 9/100",
        },
        "base_degrees": [sp.Poly(BASE, core.X, W, core.Y).degree(v)
                         for v in (core.X, W, core.Y)],
        "base_terms": len(sp.Poly(BASE, core.X, W, core.Y).terms()),
        "records": records,
        "corners": corners,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
