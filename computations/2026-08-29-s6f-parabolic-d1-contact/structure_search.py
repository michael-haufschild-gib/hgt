#!/usr/bin/env python3
"""Search exact low-rank factorizations behind parabolic D1 positivity.

Diagnostic only. No output is admissible in a Lean proof. This script does not
certify positivity; it asks whether the determinant or its leading minors have
a compact factorization in source-positive or reconstructed-gap coordinates.
"""

from __future__ import annotations

import importlib.util
import json
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


def cov_lie(expr: sp.Expr) -> sp.Expr:
    return sp.expand(core.lie3(expr) + sp.Rational(1, 2) * core.B * expr)


def factor_record(expr: sp.Expr, variables: tuple[sp.Symbol, ...]) -> dict:
    expanded = sp.expand(expr)
    poly = sp.Poly(expanded, *variables, domain=sp.QQ)
    coefficient, factors = sp.factor_list(expanded)
    return {
        "degrees": [poly.degree(v) for v in variables],
        "terms": len(poly.terms()),
        "factor_coefficient": str(coefficient),
        "factors": [{"power": power, "expression": str(factor)}
                    for factor, power in factors],
    }


def main() -> None:
    print("building normalized source jets", file=sys.stderr, flush=True)
    f = [core.Q]
    for _ in range(8):
        f.append(cov_lie(f[-1]))
    p0 = f[0] ** 2
    p2 = sp.expand(2 * (f[0] * f[2] - f[1] ** 2))
    p4 = sp.expand(2 * f[0] * f[4] - 8 * f[1] * f[3] + 6 * f[2] ** 2)
    p6 = sp.expand(2 * f[0] * f[6] - 12 * f[1] * f[5] + 30 * f[2] * f[4] - 20 * f[3] ** 2)
    p8 = sp.expand(2 * f[0] * f[8] - 16 * f[1] * f[7] + 56 * f[2] * f[6] -
                   112 * f[3] * f[5] + 70 * f[4] ** 2)
    delta2 = sp.expand(p0 * p4 - p2 ** 2)
    d1 = sp.expand(delta2 * p8 - (p0 * p6 ** 2 - 2 * p2 * p4 * p6 + p4 ** 3))

    print("factoring source-coordinate minors", file=sys.stderr, flush=True)
    source_vars = (core.U, core.B, core.Q)
    records = {
        "p2": factor_record(p2, source_vars),
        "p4": factor_record(p4, source_vars),
        "delta2": factor_record(delta2, source_vars),
        "d1": factor_record(d1, source_vars),
    }

    gap, total = sp.symbols("gap total")
    substitution = {
        core.U: total - core.B,
        core.Q: (gap - 6 + 6 * core.B**2) / 16,
    }
    print("factoring reconstructed-gap minors", file=sys.stderr, flush=True)
    gap_vars = (total, core.B, gap)
    records["delta2_gap"] = factor_record(delta2.subs(substitution), gap_vars)
    records["d1_gap"] = factor_record(d1.subs(substitution), gap_vars)

    Path("structure-results.json").write_text(json.dumps({
        "scope": "diagnostic only; forbidden as Lean input",
        "coordinates": "total=U+B, gap=16Q+6-6B^2",
        "records": records,
    }, indent=2, sort_keys=True) + "\n")
    print(json.dumps({name: {k: value[k] for k in ("degrees", "terms", "factors")}
                      for name, value in records.items()}, indent=2))


if __name__ == "__main__":
    main()
