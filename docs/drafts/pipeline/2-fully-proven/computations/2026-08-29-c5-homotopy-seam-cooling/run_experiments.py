#!/usr/bin/env python3
"""Hostile computation for the C5 likelihood-homotopy seam.

Research use only. Numeric output is never a Lean premise. Exact symbolic output
identifies candidate inequalities; dense high-precision scans try to falsify them.
"""

from __future__ import annotations

import concurrent.futures as cf
import json
import math
import os
import platform
import socket
import time
from pathlib import Path

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import mpmath as mp
import sympy as sp


OUT = Path(__file__).with_name("results.json")
NMAX = 12
DPS = 80
GRID_SIZE = 4096
A_MIN = 6.0
A_MAX = 1000.0


def spectral_point(a_text: str) -> dict[str, str]:
    """Exact theta-likelihood spectral moments and source jets at one scale."""
    mp.mp.dps = DPS
    A = mp.mpf(a_text)
    B = A - mp.mpf("1.5")
    raw = [mp.mpf(1)] + [mp.mpf(0)] * 5
    by_n: list[list[mp.mpf]] = []
    for n in range(2, NMAX + 1):
        g = mp.mpf(n * n - 1)
        prefactor = mp.exp(-mp.mpf("1.5") * g)
        atom_weight = mp.mpf(n**4)
        ray_weight = mp.mpf("1.5") * n * n * g
        row: list[mp.mpf] = []
        for k in range(6):
            ray_integral = mp.exp(-B * g) * sum(
                mp.factorial(k) / mp.factorial(j) * g**j / B ** (k - j + 1)
                for j in range(k + 1)
            )
            contribution = prefactor * (
                atom_weight * g**k * mp.exp(-B * g) + ray_weight * ray_integral
            )
            raw[k] += contribution
            row.append(contribution)
        by_n.append(row)

    P = raw[0]
    e = [value / P for value in raw]
    mean = e[1]
    k2 = e[2] - mean**2
    k3 = e[3] - 3 * mean * e[2] + 2 * mean**3
    k4 = (
        e[4]
        - 4 * mean * e[3]
        - 3 * e[2] ** 2
        + 12 * mean**2 * e[2]
        - 6 * mean**4
    )
    k5 = (
        e[5]
        - 5 * mean * e[4]
        - 10 * e[2] * e[3]
        + 20 * mean**2 * e[3]
        + 30 * mean * e[2] ** 2
        - 60 * mean**3 * e[2]
        + 24 * mean**5
    )

    f2 = 4 * A**2 * k2 - 4 * A * mean
    f3 = -8 * A**3 * k3 + 24 * A**2 * k2 - 8 * A * mean
    f4 = 16 * A**4 * k4 - 96 * A**3 * k3 + 112 * A**2 * k2 - 16 * A * mean
    f5 = (
        -32 * A**5 * k5
        + 320 * A**4 * k4
        - 800 * A**3 * k3
        + 480 * A**2 * k2
        - 32 * A * mean
    )

    b4 = 16 * (A**4 * e[4] - 6 * A**3 * e[3] + 7 * A**2 * e[2] - A * e[1])
    b5 = 32 * (
        A**5 * e[5]
        - 10 * A**4 * e[4]
        + 25 * A**3 * e[3]
        - 15 * A**2 * e[2]
        + A * e[1]
    )
    ordinary_reserve = 6 * A * b4 - b5
    reserve = f5 + 6 * A * f4

    ordinary_by_n: list[mp.mpf] = []
    for row in by_n:
        b4n = 16 * (
            A**4 * row[4] - 6 * A**3 * row[3] + 7 * A**2 * row[2] - A * row[1]
        ) / P
        b5n = 32 * (
            A**5 * row[5]
            - 10 * A**4 * row[4]
            + 25 * A**3 * row[3]
            - 15 * A**2 * row[2]
            + A * row[1]
        ) / P
        ordinary_by_n.append(6 * A * b4n - b5n)

    r2 = -f3 / (A * f2)
    r4 = -f5 / (A * f4)
    gap = 2 * r2 - r4
    source_seam = f2 * f5 - 2 * f3 * f4

    def s(value: mp.mpf) -> str:
        return mp.nstr(value, 50)

    return {
        "A": s(A),
        "P": s(P),
        "F2": s(f2),
        "F3": s(f3),
        "F4": s(f4),
        "F5": s(f5),
        "R2_negF3_over_AF2": s(r2),
        "R4_negF5_over_AF4": s(r4),
        "ratio_gap_2R2_minus_R4": s(gap),
        "source_seam_F2F5_minus_2F3F4": s(source_seam),
        "fourth_cooling_reserve_F5_plus_6AF4": s(reserve),
        "ordinary_reserve": s(ordinary_reserve),
        "bell_correction": s(reserve - ordinary_reserve),
        "n2_ordinary_reserve": s(ordinary_by_n[0]),
        "n_ge_3_ordinary_reserve": s(sum(ordinary_by_n[1:])),
    }


def worker(a_values: list[float]) -> list[dict[str, str]]:
    return [spectral_point(repr(a)) for a in a_values]


def exact_symbolics() -> dict[str, str | bool]:
    A, t, z, g, y = sp.symbols("A t z g y", positive=True)
    p2 = z**2 - z
    p3 = z**3 - 3 * z**2 + z
    p4 = z**4 - 6 * z**3 + 7 * z**2 - z
    p5 = z**5 - 10 * z**4 + 25 * z**3 - 15 * z**2 + z
    p6 = z**6 - 15 * z**5 + 65 * z**4 - 90 * z**3 + 31 * z**2 - z

    cauchy_defect = sp.factor(p4 * p6 - p5**2)

    B = A - sp.Rational(3, 2)
    h = sp.expand(3 * A * p4.subs(z, A * t) - p5.subs(z, A * t))

    def tail_integral(poly: sp.Expr, edge: sp.Expr) -> sp.Expr:
        result = 0
        for (k,), coefficient in sp.Poly(poly, t).terms():
            result += coefficient * sp.exp(-B * edge) * sum(
                sp.factorial(k) / sp.factorial(j) * edge**j / B ** (k - j + 1)
                for j in range(k + 1)
            )
        return result

    edge = sp.Integer(3)
    dominant = sp.exp(-sp.Rational(3, 2) * edge) * (
        16 * h.subs(t, edge) * sp.exp(-B * edge) + 18 * tail_integral(h, edge)
    )
    dominant_scaled = sp.factor(sp.cancel(dominant / sp.exp(-3 * A)))
    dominant_numerator = sp.factor(
        sp.together(dominant_scaled) * (2 * A - 3) ** 6 / (12 * A)
    )
    dominant_shifted = sp.Poly(sp.expand(dominant_numerator.subs(A, y + 6)), y)

    ordinary: dict[int, sp.Expr] = {}
    for k, pk in ((2, p2), (3, p3), (4, p4), (5, p5)):
        poly = pk.subs(z, A * t)
        ordinary[k] = sp.factor(
            sp.cancel(
                sp.exp(-sp.Rational(3, 2) * edge)
                * (
                    16 * poly.subs(t, edge) * sp.exp(-B * edge)
                    + 18 * tail_integral(poly, edge)
                )
                / sp.exp(-3 * A)
            )
        )
    r2_dominant = sp.factor(2 * ordinary[3] / (A * ordinary[2]))
    r4_dominant = sp.factor(2 * ordinary[5] / (A * ordinary[4]))

    a2, a3, a4, d2, d3, d4, d5 = sp.symbols("a2 a3 a4 d2 d3 d4 d5")
    seam_raw = sp.Rational(8, 3) / a2**4 * (
        9 * a2**4 * d2**2 * d5
        - 18 * a2**4 * d2 * d3 * d4
        + 2 * a2**3 * d3 * d4**2
        - 2 * a2**2 * a3 * d2 * d4**2
        - 4 * a2**2 * a4 * d2 * d3 * d4
        + 4 * a2 * a3 * a4 * d2**2 * d4
        + 2 * a2 * a4**2 * d2**2 * d3
        - 2 * a3 * a4**2 * d2**3
    )
    x = -d3 / d2
    yy = d4 / d2
    zz = -d5 / d2
    r = a3 / a2
    ss = a4 / a2
    seam_factored = sp.Rational(8, 3) * d2**3 * (
        9 * (2 * x * yy - zz) + 2 * (x + r) * (yy - ss) ** 2 / (-a2)
    )

    return {
        "pointwise_cauchy_defect": str(cauchy_defect),
        "dominant_n2_reserve_scaled": str(dominant_scaled),
        "dominant_n2_reserve_numerator": str(dominant_numerator),
        "dominant_n2_numerator_shift_A_minus_6": str(dominant_shifted.as_expr()),
        "dominant_n2_R2_asymptotic": str(sp.series(r2_dominant, A, sp.oo, 5)),
        "dominant_n2_R4_asymptotic": str(sp.series(r4_dominant, A, sp.oo, 5)),
        "dominant_n2_ratio_gap_asymptotic": str(
            sp.series(2 * r2_dominant - r4_dominant, A, sp.oo, 5)
        ),
        "seam_factorization_verified": sp.simplify(seam_raw - seam_factored) == 0,
        "seam_factored": str(seam_factored),
    }


def main() -> None:
    started = time.time()
    workers = min(32, os.cpu_count() or 1)
    grid = [
        A_MIN * (A_MAX / A_MIN) ** (index / (GRID_SIZE - 1))
        for index in range(GRID_SIZE)
    ]
    chunks = [grid[index::workers] for index in range(workers)]
    with cf.ProcessPoolExecutor(max_workers=workers) as pool:
        rows = [row for block in pool.map(worker, chunks) for row in block]
    rows.sort(key=lambda row: mp.mpf(row["A"]))

    def numeric(row: dict[str, str], key: str) -> mp.mpf:
        return mp.mpf(row[key])

    extrema = {
        "min_R2": min(rows, key=lambda row: numeric(row, "R2_negF3_over_AF2")),
        "max_R4": max(rows, key=lambda row: numeric(row, "R4_negF5_over_AF4")),
        "min_ratio_gap": min(rows, key=lambda row: numeric(row, "ratio_gap_2R2_minus_R4")),
        "min_bell_correction": min(rows, key=lambda row: numeric(row, "bell_correction")),
        "max_abs_tail_over_n2_ordinary_reserve": max(
            rows,
            key=lambda row: abs(numeric(row, "n_ge_3_ordinary_reserve"))
            / numeric(row, "n2_ordinary_reserve"),
        ),
    }
    extrema["max_abs_tail_over_n2_ordinary_reserve"]["abs_tail_over_n2"] = mp.nstr(
        abs(numeric(extrema["max_abs_tail_over_n2_ordinary_reserve"], "n_ge_3_ordinary_reserve"))
        / numeric(extrema["max_abs_tail_over_n2_ordinary_reserve"], "n2_ordinary_reserve"),
        50,
    )

    monotonic = {
        "R2_decrease_count": sum(
            numeric(rows[i + 1], "R2_negF3_over_AF2")
            < numeric(rows[i], "R2_negF3_over_AF2")
            for i in range(len(rows) - 1)
        ),
        "R4_decrease_count": sum(
            numeric(rows[i + 1], "R4_negF5_over_AF4")
            < numeric(rows[i], "R4_negF5_over_AF4")
            for i in range(len(rows) - 1)
        ),
        "ratio_gap_increase_count": sum(
            numeric(rows[i + 1], "ratio_gap_2R2_minus_R4")
            > numeric(rows[i], "ratio_gap_2R2_minus_R4")
            for i in range(len(rows) - 1)
        ),
    }

    anchors = [spectral_point(str(a)) for a in (6, 7, 10, 20, 50, 100, 1000)]
    payload = {
        "purpose": "Kill or sharpen the C5 likelihood-homotopy seam route; never a Lean premise.",
        "environment": {
            "host": socket.gethostname(),
            "python": platform.python_version(),
            "cpu_count": os.cpu_count(),
            "workers": workers,
            "mpmath_dps": DPS,
            "nmax": NMAX,
        },
        "grid": {"size": GRID_SIZE, "A_min": A_MIN, "A_max": A_MAX, "spacing": "log"},
        "exact_symbolics": exact_symbolics(),
        "extrema": extrema,
        "monotonic_checks": monotonic,
        "anchors": anchors,
        "elapsed_seconds": time.time() - started,
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
