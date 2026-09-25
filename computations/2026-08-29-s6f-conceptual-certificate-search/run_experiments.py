#!/usr/bin/env python3
"""Search for a short exact S6F thin-cone positivity decomposition.

Diagnostic only. No output from this script is admissible in a Lean proof.

The already formalized orbit inequalities motivate danger-coordinate slacks

    s = X - 191/10,
    w = 9/100 - z^2,
    h = y - 2/5,

with s,w,h >= 0 and h <= 1/10.  This script tests the unknown claim that
endpoint walls, coordinate derivatives, or the concavity chord remainder become
short positive polynomials in these slacks.  It reports structure and hashes,
not a coefficient table intended for formal use.
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

S, W, H, U2 = sp.symbols("s w h u")
X0 = sp.Rational(191, 10)
Z2MAX = sp.Rational(9, 100)
YA = sp.Rational(2, 5)
YB = sp.Rational(1, 2)


def certificate() -> sp.Expr:
    drift = core.normalized_drift()
    triangle = sp.expand(drift.subs(core.V, core.Z * core.Y))
    quotient = sp.cancel(triangle / core.Z)
    assert sp.denom(quotient) == 1
    return sp.expand(quotient)


Terms = dict[tuple[int, ...], sp.Rational]


def add_term(out: Terms, powers: tuple[int, ...], value: sp.Rational) -> None:
    if value == 0:
        return
    updated = out.get(powers, sp.Rational(0)) + value
    if updated == 0:
        out.pop(powers, None)
    else:
        out[powers] = updated


def even_terms(expr: sp.Expr) -> Terms:
    out: Terms = {}
    for (ex, ez, ey), value in sp.Poly(
        expr, core.X, core.Z, core.Y, domain=sp.QQ
    ).terms():
        assert ez % 2 == 0
        out[(ex, ez // 2, ey)] = value
    return out


def affine_axis(terms: Terms, axis: int, shift: sp.Rational, sign: int) -> Terms:
    """Exact sparse substitution old=shift+sign*new along one axis."""
    out: Terms = {}
    for powers, value in terms.items():
        exponent = powers[axis]
        for k in range(exponent + 1):
            changed = list(powers)
            changed[axis] = k
            coefficient = (
                value * sp.binomial(exponent, k) * shift ** (exponent - k) * sign**k
            )
            add_term(out, tuple(changed), coefficient)
    return out


def derivative(terms: Terms, axis: int, order: int = 1, sign: int = 1) -> Terms:
    out = terms
    for _ in range(order):
        changed: Terms = {}
        for powers, value in out.items():
            exponent = powers[axis]
            if exponent == 0:
                continue
            target = list(powers)
            target[axis] -= 1
            add_term(changed, tuple(target), exponent * value)
        out = changed
    if sign == -1:
        return {powers: -value for powers, value in out.items()}
    return out


def wall(terms: Terms, h: sp.Rational) -> Terms:
    out: Terms = {}
    for (i, j, k), value in terms.items():
        add_term(out, (i, j), value * h**k)
    return out


def chord_remainder(terms: Terms, length: sp.Rational) -> Terms:
    """Divide C minus its endpoint chord by h*(length-h), fibrewise."""
    grouped: dict[tuple[int, int], dict[int, sp.Rational]] = {}
    for (i, j, k), value in terms.items():
        grouped.setdefault((i, j), {})[k] = value
    out: Terms = {}
    for (i, j), coeff in grouped.items():
        degree = max(coeff)
        lower = coeff.get(0, sp.Rational(0))
        upper = sum(value * length**k for k, value in coeff.items())
        residual = {k: coeff.get(k, sp.Rational(0)) for k in range(degree + 1)}
        residual[0] -= lower
        residual[1] -= (upper - lower) / length
        assert residual[0] == 0
        quotient: dict[int, sp.Rational] = {}
        quotient[0] = residual[1] / length
        for r in range(2, degree):
            quotient[r - 1] = (residual[r] + quotient[r - 2]) / length
        assert residual[degree] == -quotient[degree - 2]
        for k, value in quotient.items():
            add_term(out, (i, j, k), value)
    return out


def coeff_summary(terms: Terms, dimensions: int) -> dict:
    ordered = sorted(terms.items(), reverse=True)
    coeffs = [value for _, value in ordered]
    digest = hashlib.sha256(
        "\n".join(f"{powers}:{value}" for powers, value in ordered).encode("ascii")
    ).hexdigest()
    return {
        "degrees": [max(p[axis] for p in terms) for axis in range(dimensions)],
        "terms": len(coeffs),
        "negative": sum(bool(c < 0) for c in coeffs),
        "positive": sum(bool(c > 0) for c in coeffs),
        "minimum": str(min(coeffs)),
        "maximum": str(max(coeffs)),
        "sha256": digest,
    }


def matrix_rank_summary(terms: Terms) -> dict:
    rows = max(i for i, _ in terms) + 1
    cols = max(j for _, j in terms) + 1
    matrix = sp.zeros(rows, cols)
    for (i, j), value in terms.items():
        matrix[i, j] = value
    return {"shape": [rows, cols], "rank": int(matrix.rank())}


def analyze_job(task: tuple[str, Terms, int]) -> tuple[str, dict]:
    name, terms, dimensions = task
    result = {"power": coeff_summary(terms, dimensions)}
    if dimensions == 2:
        result["coefficient_matrix"] = matrix_rank_summary(terms)
    return name, result


def main() -> None:
    global YA, YB
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(6, os.cpu_count() or 1))
    parser.add_argument("--sharp", action="store_true")
    args = parser.parse_args()

    if args.sharp:
        YA = sp.Rational(13, 32)
        YB = sp.Rational(7, 16)

    print("reconstructing exact certificate", file=sys.stderr, flush=True)
    c = certificate()
    print("certificate reconstructed", file=sys.stderr, flush=True)
    print("forming danger-coordinate slacks", file=sys.stderr, flush=True)
    transformed = even_terms(c)
    transformed = affine_axis(transformed, 0, X0, 1)
    transformed = affine_axis(transformed, 1, Z2MAX, -1)
    transformed = affine_axis(transformed, 2, YA, 1)
    print("slacks formed", file=sys.stderr, flush=True)

    lower = wall(transformed, sp.Rational(0))
    upper = wall(transformed, YB - YA)
    remainder = chord_remainder(transformed, YB - YA)
    dc_dx = derivative(transformed, 0)
    minus_dc_du = derivative(transformed, 1)
    minus_d2c_dy2 = derivative(transformed, 2, order=2, sign=-1)

    tasks = [
        ("lower_wall", lower, 2),
        ("upper_wall", upper, 2),
        ("chord_remainder", remainder, 3),
        ("dC_dX", dc_dx, 3),
        ("minus_dC_du", minus_dc_du, 3),
        ("minus_d2C_dy2", minus_d2c_dy2, 3),
        ("C", transformed, 3),
    ]
    print("summarizing exact coefficient signs", file=sys.stderr, flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = dict(pool.map(analyze_job, tasks))
    print("summaries complete", file=sys.stderr, flush=True)

    # Small exact corner values are legitimate discovery targets for later
    # independent hand derivation, but are never imported into Lean.
    corners = {
        "lower_X0_zmax": str(lower[(0, 0)]),
        "upper_X0_zmax": str(upper[(0, 0)]),
    }

    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers": args.workers,
        "coordinate_slacks": f"s=X-191/10, w=9/100-z^2, h=y-{YA}",
        "upper_y": str(YB),
        "certificate_terms": len(sp.Poly(c, core.X, core.Z, core.Y).terms()),
        "certificate_even_in_z": True,
        "records": records,
        "corner_values": corners,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
