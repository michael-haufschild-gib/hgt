#!/usr/bin/env python3
"""Independent exact verifier for the parabolic D1 hostile computation.

Diagnostic only. No result is admissible in a Lean proof. This verifier
rebuilds the determinant from a matrix, reconstructs normalized coordinates,
uses a separately implemented staged Bernstein transform, and checks selected
digests plus the exact outer-face root count.
"""

from __future__ import annotations

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
spec = importlib.util.spec_from_file_location("s6f_core_verify", CORE_PATH)
core = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = core
spec.loader.exec_module(core)

W, ETA = sp.symbols("w eta")
X0, K, WMAX = sp.Rational(191, 10), sp.Rational(147, 20), sp.Rational(9, 100)
PRISM: sp.Expr | None = None


def rebuild() -> sp.Expr:
    def cov(expr: sp.Expr) -> sp.Expr:
        return sp.expand(core.lie3(expr) + sp.Rational(1, 2) * core.B * expr)

    f = [core.Q]
    for _ in range(8):
        f.append(cov(f[-1]))
    moments = [
        f[0] ** 2,
        2 * (f[0] * f[2] - f[1] ** 2),
        2 * f[0] * f[4] - 8 * f[1] * f[3] + 6 * f[2] ** 2,
        2 * f[0] * f[6] - 12 * f[1] * f[5] + 30 * f[2] * f[4] - 20 * f[3] ** 2,
        2 * f[0] * f[8] - 16 * f[1] * f[7] + 56 * f[2] * f[6] -
            112 * f[3] * f[5] + 70 * f[4] ** 2,
    ]
    determinant = sp.expand(sp.Matrix([
        [moments[0], moments[1], moments[2]],
        [moments[1], moments[2], moments[3]],
        [moments[2], moments[3], moments[4]],
    ]).det())
    q = (core.R**2 * (1 - core.Z**2 + sp.Rational(2, 3) *
         (core.Z - core.V) ** 2) - 6) / 16
    transformed = sp.Poly(sp.expand(determinant.subs({
        core.U: core.R * core.V,
        core.B: core.R * (core.Z - core.V) / 3,
        core.Q: q,
    })), core.R, core.V, core.Z, domain=sp.QQ)
    normalized = 0
    for (er, ev, ez), coefficient in transformed.terms():
        assert er % 2 == 0
        normalized += coefficient * core.X**(er // 2) * core.V**ev * core.Z**ez
    triangle = sp.Poly(sp.expand(normalized.subs(core.V, core.Z * core.Y)),
                       core.X, core.Z, core.Y, domain=sp.QQ)
    base = 0
    for (ex, ez, ey), coefficient in triangle.terms():
        assert ez % 2 == 0
        base += coefficient * core.X**ex * W**(ez // 2) * core.Y**ey
    y = sp.Rational(13, 32) + W / 32 + ETA * (sp.Rational(1, 160) + 5 * W / 96)
    return sp.expand(base.subs({core.X: X0 + K * W + core.S, core.Y: y}))


def elevate_univariate(power: list[sp.Rational]) -> list[sp.Rational]:
    degree = len(power) - 1
    return [sum(power[i] * sp.binomial(k, i) / sp.binomial(degree, i)
                for i in range(k + 1)) for k in range(degree + 1)]


def staged_coefficients(expr: sp.Expr) -> list[sp.Rational]:
    unit = sp.Poly(sp.expand(expr.subs(W, WMAX * core.T)),
                   core.S, core.T, ETA, domain=sp.QQ)
    ds = unit.degree(core.S)
    out = []
    for es in range(ds + 1):
        section = sp.Poly(sum(coefficient * core.T**et * ETA**ee
            for (section_s, et, ee), coefficient in unit.terms() if section_s == es),
            core.T, ETA, domain=sp.QQ)
        dt, de = section.degree(core.T), section.degree(ETA)
        eta_power_by_t = []
        for et in range(dt + 1):
            eta_power = [section.coeff_monomial(core.T**et * ETA**ee)
                         for ee in range(de + 1)]
            eta_power_by_t.append(elevate_univariate(eta_power))
        for kt in range(dt + 1):
            for ke in range(de + 1):
                out.append(sum(eta_power_by_t[it][ke] * sp.binomial(kt, it) /
                               sp.binomial(dt, it) for it in range(kt + 1)))
    return out


def verify_job(kind: str) -> tuple[str, str, int, int, int]:
    assert PRISM is not None
    if kind == "value":
        expr = PRISM
    elif kind == "dS":
        expr = sp.diff(PRISM, core.S)
    elif kind == "d2W":
        expr = sp.diff(PRISM, W, 2)
    elif kind == "d3W":
        expr = sp.diff(PRISM, W, 3)
    else:
        raise ValueError(kind)
    values = staged_coefficients(expr)
    digest = hashlib.sha256("\n".join(str(v) for v in values).encode("ascii")).hexdigest()
    return (kind, digest, sum(bool(v < 0) for v in values),
            sum(bool(v == 0) for v in values), sum(bool(v > 0) for v in values))


def main() -> None:
    expected = json.loads((HERE / "results.json").read_text())
    hierarchy = json.loads((HERE / "hierarchy-results.json").read_text())
    print("independently rebuilding parabolic determinant", file=sys.stderr, flush=True)
    global PRISM
    PRISM = rebuild()
    kinds = ["value", "dS", "d2W", "d3W"]
    with concurrent.futures.ProcessPoolExecutor(max_workers=min(4, os.cpu_count() or 1)) as pool:
        records = dict((name, (digest, neg, zero, pos))
                       for name, digest, neg, zero, pos in pool.map(verify_job, kinds))
    for name, (digest, neg, zero, pos) in records.items():
        record = expected["records"][name]
        assert digest == record["bernstein_sha256"]
        assert (neg, zero, pos) == tuple(record["bernstein"][key]
                                         for key in ("negative", "zero", "positive"))

    outer = sp.Poly(PRISM.subs({core.S: 0, W: WMAX}), ETA, domain=sp.QQ)
    derivative = outer.diff()
    assert sp.count_roots(derivative.as_expr(), 0, 1) == 0
    assert derivative.eval(0) < 0 and derivative.eval(1) < 0
    assert outer.eval(1) > 0
    order4 = hierarchy["records"]["4"]["bernstein"]
    assert order4["negative"] > 0 and order4["positive"] > 0
    print("verified: direct D1 positive and scale-increasing; clock concavity survives, order-4 hierarchy fails; outer minimum is upper corner")


if __name__ == "__main__":
    main()
