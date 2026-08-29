#!/usr/bin/env python3
"""Exact normalized-chamber search for S6F projective drift.

Diagnostic only; no result is admissible as input to a Lean proof.

Transforms the literal source-positive drift from (U,B,Q) to physical
normalized clocks

  X = R^2,  v = U/R,  z = -Z,
  U = R v,
  B = R (z-v)/3,
  Q = (X * (1-z^2 + 2/3*(z-v)^2) - 6) / 16.

The proved physical simplex is 191/10 < X < 20 and 0 < v < z < 1.
The script tests whether a sharper rational cap on z exposes an exact
coefficient or tensor-Bernstein positivity certificate.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import math
import os
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as sp


U, B, Q = sp.symbols("U B Q")
R, X, V, Z = sp.symbols("R X V Z")
S, T, Y = sp.symbols("S T Y")


def lie3(expr: sp.Expr) -> sp.Expr:
    gap = 16 * Q + 6 - 6 * B**2
    vf = {
        U: sp.Rational(9, 2) + 4 * Q + sp.Rational(3, 2) * B**2 + 2 * B * U,
        B: sp.Rational(1, 2) + 4 * Q - sp.Rational(1, 2) * B**2,
        Q: sp.Rational(3, 4) * B * (sp.Rational(1, 2) + 4 * Q - sp.Rational(1, 2) * B**2)
        - sp.Rational(1, 8) * gap * (U + B),
    }
    return sp.expand(sum(sp.diff(expr, var) * vf[var] for var in (U, B, Q)))


def source_positive_drift() -> sp.Expr:
    def cov_lie(expr: sp.Expr) -> sp.Expr:
        return sp.expand(lie3(expr) + sp.Rational(1, 2) * B * expr)

    f = [Q]
    for _ in range(8):
        f.append(cov_lie(f[-1]))
    p0 = f[0] ** 2
    p2 = 2 * (f[0] * f[2] - f[1] ** 2)
    p4 = 2 * f[0] * f[4] - 8 * f[1] * f[3] + 6 * f[2] ** 2
    p6 = 2 * f[0] * f[6] - 12 * f[1] * f[5] + 30 * f[2] * f[4] - 20 * f[3] ** 2
    p8 = 2 * f[0] * f[8] - 16 * f[1] * f[7] + 56 * f[2] * f[6] - 112 * f[3] * f[5] + 70 * f[4] ** 2
    d1 = sp.expand(p0 * p4 * p8 - p0 * p6**2 - p2**2 * p8 + 2 * p2 * p4 * p6 - p4**3)
    return sp.expand(Q * lie3(d1) - 6 * d1 * lie3(Q))


def eliminate_scale_parity(expr: sp.Expr) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), R, V, Z, domain=sp.QQ)
    result = 0
    for (er, ev, ez), coeff in poly.terms():
        assert er >= 1 and er % 2 == 1
        result += coeff * X ** ((er - 1) // 2) * V**ev * Z**ez
    return sp.expand(result)


def normalized_drift() -> sp.Expr:
    qexpr = (R**2 * (1 - Z**2 + sp.Rational(2, 3) * (Z - V) ** 2) - 6) / 16
    transformed = sp.expand(
        source_positive_drift().subs({U: R * V, B: R * (Z - V) / 3, Q: qexpr})
    )
    return eliminate_scale_parity(transformed)


def bernstein_tensor(poly: sp.Expr, variables: tuple[sp.Symbol, ...]):
    p = sp.Poly(sp.expand(poly), *variables, domain=sp.QQ)
    degrees = tuple(p.degree(var) for var in variables)
    shape = tuple(degree + 1 for degree in degrees)
    coeff = np.empty(shape, dtype=object)
    coeff.fill(sp.Rational(0))
    for powers, value in p.terms():
        coeff[powers] = value
    for axis, degree in enumerate(degrees):
        changed = np.empty_like(coeff)
        for index in np.ndindex(*(shape[:axis] + shape[axis + 1 :])):
            before = list(index[:axis])
            after = list(index[axis:])
            for k in range(degree + 1):
                total = sp.Rational(0)
                for i in range(k + 1):
                    pos = tuple(before + [i] + after)
                    total += coeff[pos] * sp.binomial(k, i) / sp.binomial(degree, i)
                changed[tuple(before + [k] + after)] = sp.factor(total)
        coeff = changed
    flat = list(coeff.flat)
    minimum = min(flat)
    minimum_flat_index = flat.index(minimum)
    coefficient_sha256 = hashlib.sha256(
        "\n".join(str(value) for value in flat).encode("ascii")
    ).hexdigest()
    negative = sum(bool(value < 0) for value in flat)
    zero = sum(bool(value == 0) for value in flat)
    return {
        "degrees": degrees,
        "count": len(flat),
        "negative_count": negative,
        "zero_count": zero,
        "positive": negative == 0 and zero == 0,
        "nonnegative": negative == 0,
        "minimum": str(minimum),
        "minimum_index": tuple(int(i) for i in np.unravel_index(minimum_flat_index, shape)),
        "maximum": str(max(flat)),
        "coefficient_sha256": coefficient_sha256,
    }


def cap_record(base: sp.Expr, cap: sp.Rational) -> dict:
    cube = sp.expand(
        base.subs(
            {
                X: sp.Rational(191, 10) + sp.Rational(9, 10) * S,
                Z: cap * T,
            }
        )
    )
    power = sp.Poly(cube, S, T, Y, domain=sp.QQ)
    power_coeff = power.coeffs()
    return {
        "z_cap": str(cap),
        "term_count": len(power.terms()),
        "power_coeff_negative_count": sum(bool(c < 0) for c in power_coeff),
        "power_coeff_zero_count": sum(bool(c == 0) for c in power_coeff),
        "power_coeff_nonnegative": all(bool(c >= 0) for c in power_coeff),
        "bernstein": bernstein_tensor(cube, (S, T, Y)),
    }


def cap_record_job(task: tuple[sp.Expr, sp.Rational]) -> dict:
    return cap_record(*task)


def random_attack(base: sp.Expr, count: int, seed: int) -> dict:
    fn = sp.lambdify((X, Z, Y), base, modules="numpy", cse=True)
    rng = np.random.default_rng(seed)
    chunk = 200_000
    minimum = math.inf
    witness = None
    eligible = 0
    for start in range(0, count, chunk):
        size = min(chunk, count - start)
        xv = 19.1 + 0.9 * rng.random(size)
        zv = rng.random(size)
        yv = rng.random(size)
        vv = zv * yv
        qfactor = xv * (1 - zv**2 + (2.0 / 3.0) * (zv - vv) ** 2) - 6
        mask = qfactor > 0
        values = np.asarray(fn(xv, zv, yv), dtype=np.float64)
        values = np.where(mask, values, np.inf)
        eligible += int(np.count_nonzero(mask))
        idx = int(np.argmin(values))
        if values[idx] < minimum:
            minimum = float(values[idx])
            witness = {"X": float(xv[idx]), "z": float(zv[idx]), "y": float(yv[idx])}
    return {
        "samples": count,
        "eligible_Q_positive": eligible,
        "minimum": minimum,
        "witness": witness,
    }


def actual_endpoint() -> dict:
    mp.mp.dps = 50
    # X=R^2 and R=pi*theta_3(i)^4=Gamma(1/4)^4/(4*pi^2).
    x0 = mp.gamma(mp.mpf(1) / 4) ** 8 / (16 * mp.pi**4)

    def rhs(_x, state):
        scale, v, z = state
        root = mp.sqrt(scale)
        return [
            mp.mpf(4) / 3 * scale * root * (z - v),
            (3 + scale * (1 - z**2) / 4 + scale * (z - v) ** 2 / 3) / root,
            root * (1 - z**2),
        ]

    solution = mp.odefun(rhs, 0, (x0, mp.mpf(0), mp.mpf(0)), tol=mp.mpf("1e-35"), degree=40)
    end = mp.mpf(137) / 2000
    scale, v, z = solution(end)
    return {
        "x": str(end),
        "seam_X": mp.nstr(x0, 40),
        "endpoint_X": mp.nstr(scale, 40),
        "endpoint_v": mp.nstr(v, 40),
        "endpoint_z": mp.nstr(z, 40),
        "z_lt_one_third": bool(z < mp.mpf(1) / 3),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--random", type=int, default=2_000_000)
    parser.add_argument("--seed", type=int, default=20260829)
    parser.add_argument("--workers", type=int, default=min(5, os.cpu_count() or 1))
    args = parser.parse_args()

    drift = normalized_drift()
    triangle = sp.expand(drift.subs(V, Z * Y))
    triangle_poly = sp.Poly(triangle, Z)
    assert triangle_poly.nth(0) == 0
    base = sp.cancel(triangle / Z)
    assert sp.denom(base) == 1
    base = sp.expand(base)
    caps = (
        sp.Rational(1),
        sp.Rational(1, 2),
        sp.Rational(1, 3),
        sp.Rational(3, 10),
        sp.Rational(1, 4),
    )
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        cap_results = list(pool.map(cap_record_job, ((base, cap) for cap in caps)))
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "sympy": sp.__version__,
        "normalized_drift_degree": sp.Poly(drift, X, V, Z).total_degree(),
        "normalized_drift_terms": len(sp.Poly(drift, X, V, Z).terms()),
        "triangle_factor": "drift / R = z * certificate(X,z,y), v=z*y",
        "certificate_degree": sp.Poly(base, X, Z, Y).total_degree(),
        "certificate_terms": len(sp.Poly(base, X, Z, Y).terms()),
        "random_full_simplex": random_attack(base, args.random, args.seed),
        "workers": args.workers,
        "caps": cap_results,
        "actual_endpoint_ode": actual_endpoint(),
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
