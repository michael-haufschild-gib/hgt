#!/usr/bin/env python3
"""Independent exact verifier for selected parabolic-cone sign claims.

Diagnostic only. No output is admissible in a Lean proof.
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

W = sp.Symbol("verify_w")
X0 = sp.Rational(191, 10)
K = sp.Rational(147, 20)
YA = sp.Rational(13, 32)
WMAX = sp.Rational(9, 100)
WALL: sp.Expr | None = None


def rebuild_wall() -> sp.Expr:
    drift = core.normalized_drift()
    c = sp.cancel(sp.expand(drift.subs(core.V, core.Z * core.Y)) / core.Z)
    assert sp.denom(c) == 1
    poly = sp.Poly(sp.expand(c), core.X, core.Z, core.Y, domain=sp.QQ)
    even = sp.Rational(0)
    for (ex, ez, ey), coeff in poly.terms():
        assert ez % 2 == 0
        even += coeff * core.X**ex * W**(ez // 2) * core.Y**ey
    return sp.expand(even.subs({
        core.X: X0 + K * W + core.S,
        core.Y: YA + W / 32,
    }))


def bernstein_digest(expr: sp.Expr) -> tuple[dict, str]:
    unit = sp.Poly(sp.expand(expr.subs(W, WMAX * core.T)), core.S, core.T, domain=sp.QQ)
    fibres: dict[int, dict[int, sp.Rational]] = {}
    for (es, et), coeff in unit.terms():
        fibres.setdefault(es, {})[et] = coeff
    values: list[sp.Rational] = []
    for es in sorted(fibres):
        degree = max(fibres[es])
        powers = [fibres[es].get(i, sp.Rational(0)) for i in range(degree + 1)]
        for j in range(degree + 1):
            values.append(sum(
                powers[i] * sp.binomial(j, i) / sp.binomial(degree, i)
                for i in range(j + 1)
            ))
    stats = {
        "count": len(values),
        "negative": sum(bool(v < 0) for v in values),
        "zero": sum(bool(v == 0) for v in values),
        "positive": sum(bool(v > 0) for v in values),
    }
    digest = hashlib.sha256("\n".join(str(v) for v in values).encode("ascii")).hexdigest()
    return stats, digest


def verify_one(order: int) -> tuple[str, dict, str]:
    assert WALL is not None
    expr = (-1) ** order * sp.diff(WALL, W, order)
    stats, digest = bernstein_digest(expr)
    return f"formal_alt_derivative_{order}", stats, digest


def main() -> None:
    expected = json.loads((HERE / "results.json").read_text())
    global WALL
    WALL = rebuild_wall()
    orders = [0, 1, 2, 3, 13]
    with concurrent.futures.ProcessPoolExecutor(max_workers=min(5, os.cpu_count() or 1)) as pool:
        records = list(pool.map(verify_one, orders))
    for name, stats, digest in records:
        want = expected["records"][name]
        for key in ("count", "negative", "zero", "positive"):
            assert stats[key] == want["bernstein"][key], (name, key, stats[key], want["bernstein"][key])
        assert digest == want["bernstein_sha256"], name
    assert expected["records"]["formal_alt_derivative_0"]["bernstein"]["negative"] == 0
    assert expected["records"]["formal_alt_derivative_1"]["bernstein"]["negative"] == 0
    assert expected["records"]["formal_alt_derivative_2"]["bernstein"]["negative"] == 0
    assert expected["records"]["formal_alt_derivative_3"]["bernstein"]["negative"] > 0
    assert sp.Rational(expected["corners"]["outer_floor"]) > 0
    assert sp.Rational(expected["corners"]["outer_floor_dW"]) < 0
    print("verified: parabolic wall is positive/decreasing/convex; alternating order 3 fails")


if __name__ == "__main__":
    main()
