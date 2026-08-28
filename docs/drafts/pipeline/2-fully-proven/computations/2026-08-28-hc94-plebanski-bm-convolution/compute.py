#!/usr/bin/env python3
"""Exploratory HC94 hypergeometric--Plebanski convolution scan.

Computational route-selection evidence only. Nothing here is imported by Lean or used as proof.
Formulas are transcribed from the corpus modules listed in REPORT.md.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import os
import platform
import time
from pathlib import Path

import mpmath as mp


ZERO_HEIGHTS = [
    "14.134725141734693790457251983562470270784257115699",
    "21.022039638771554992628479593896902777334340524903",
    "25.010857580145688763213790992562821818659549672558",
]


def cstr(z: mp.mpc, digits: int = 50) -> dict[str, str]:
    return {"re": mp.nstr(mp.re(z), digits), "im": mp.nstr(mp.im(z), digits)}


def rho_to_chi(rho: mp.mpc) -> mp.mpc:
    # Corpus: chi = i (1-rho)/2 after rho(xiSpectralPoint(q)) = q.
    return mp.j * (1 - rho) / 2


def bm_outer_parameters(n: int, rho: mp.mpc) -> tuple[mp.mpc, mp.mpc, mp.mpc]:
    chi = rho_to_chi(rho)
    a = -2 * n - mp.mpf(5) / 4 - mp.j * chi / 2
    b = -2 * n - mp.mpf(5) / 4 - 3 * mp.j * chi / 2
    return a, b, mp.mpf(1) / 2


def bm_original_c(n: int, rho: mp.mpc) -> mp.mpc:
    chi = rho_to_chi(rho)
    return -4 * n - 2 - 2 * mp.j * chi


def forbidden_connection(n: int, rho: mp.mpc) -> mp.mpc:
    """Exact forbidden/source coefficient of horizon-regular BM ++ solution."""
    chi = rho_to_chi(rho)
    radial_a = -2 * n - mp.mpf(3) / 4 - mp.j * chi / 2
    radial_b = -2 * n - mp.mpf(3) / 4 - 3 * mp.j * chi / 2
    return mp.gamma(bm_original_c(n, rho)) * mp.gamma(mp.mpf(1) / 2) / (
        mp.gamma(radial_a) * mp.gamma(radial_b)
    )


def physical_weights(n: int, rho: mp.mpc) -> tuple[mp.mpc, mp.mpc]:
    # Response dilation exponent i*omega_pp = 4n+2+rho.
    # Fundamental negative-branch dilation exponent is -2*alpha_minus = 2-rho/2.
    return 4 * n + 2 + rho, 2 - rho / 2


def charges(model: str, rho: mp.mpc) -> tuple[mp.mpc, mp.mpc]:
    # h is doubled ++ response charge. k alternatives expose unresolved full-metric assignment.
    h = rho
    if model == "reflected":
        return h, 1 - rho / 2
    if model == "same":
        return h, h
    if model == "opposite":
        return h, -h
    raise ValueError(model)


def weighted_outer_integral(j: int, n: int, rho: mp.mpc) -> mp.mpc:
    """Beta-weighted corner-renormalized forbidden hypergeometric factor.

    After w=1-t:
      integral t^(alpha+j-1)(1-t)^(beta-1) 2F1(a,b;1/2;1-t) dt
      = B(beta,alpha+j) 3F2(a,b,beta;1/2,alpha+beta+j;1).
    """
    a, b, c0 = bm_outer_parameters(n, rho)
    alpha, beta = physical_weights(n, rho)
    return mp.beta(beta, alpha + j) * mp.hyper(
        [a, b, beta], [c0, alpha + beta + j], 1
    )


def weighted_outer_integral_quad(j: int, n: int, rho: mp.mpc) -> mp.mpc:
    a, b, c0 = bm_outer_parameters(n, rho)
    alpha, beta = physical_weights(n, rho)

    def integrand(w: mp.mpf) -> mp.mpc:
        return (
            w ** (beta - 1)
            * (1 - w) ** (alpha + j - 1)
            * mp.hyp2f1(a, b, c0, w)
        )

    return mp.quad(integrand, [0, mp.mpf("0.25"), mp.mpf("0.75"), 1])


def convolution(
    n: int, rho: mp.mpc, charge_model: str, curvature: mp.mpc
) -> tuple[mp.mpc, mp.mpc, mp.mpc]:
    h, k = charges(charge_model, rho)
    i0 = weighted_outer_integral(0, n, rho)
    i1 = weighted_outer_integral(1, n, rho)
    i2 = weighted_outer_integral(2, n, rho)
    p2 = (h + k) ** 2
    p1 = -2 * h * (h + k) - curvature * (h - k) * (h + k)
    p0 = h**2 + curvature * (h - k) * h
    reduced = (p2 * i2 + p1 * i1 + p0 * i0) / 2
    connection = forbidden_connection(n, rho)
    return connection * reduced, reduced, connection


def convolution_from_integrals(
    n: int,
    rho: mp.mpc,
    charge_model: str,
    curvature: mp.mpc,
    integrals: tuple[mp.mpc, mp.mpc, mp.mpc],
    connection: mp.mpc,
) -> tuple[mp.mpc, mp.mpc]:
    h, k = charges(charge_model, rho)
    i0, i1, i2 = integrals
    p2 = (h + k) ** 2
    p1 = -2 * h * (h + k) - curvature * (h - k) * (h + k)
    p0 = h**2 + curvature * (h - k) * h
    reduced = (p2 * i2 + p1 * i1 + p0 * i0) / 2
    return connection * reduced, reduced


def corner_finite_part(n: int, rho: mp.mpc) -> mp.mpc:
    a, b, c0 = bm_outer_parameters(n, rho)
    return forbidden_connection(n, rho) * a * (a + 1) * b * (b + 1) / (
        c0 * (c0 + 1)
    )


def evaluate_case_from_data(
    n: int,
    rho: mp.mpc,
    model: str,
    integrals: tuple[mp.mpc, mp.mpc, mp.mpc],
    connection: mp.mpc,
    finite: mp.mpc,
) -> dict:
    value0, reduced0 = convolution_from_integrals(
        n, rho, model, mp.mpf(0), integrals, connection
    )
    value1, reduced1 = convolution_from_integrals(
        n, rho, model, mp.mpf(1), integrals, connection
    )
    slope = value1 - value0
    curvature_zero = None if slope == 0 else -value0 / slope
    return {
        "n": n,
        "rho": cstr(rho),
        "chi": cstr(rho_to_chi(rho)),
        "charge_model": model,
        "weights": [cstr(x) for x in physical_weights(n, rho)],
        "charges": [cstr(x) for x in charges(model, rho)],
        "connection": cstr(connection),
        "corner_finite_part": cstr(finite),
        "convolution_curvature_0": cstr(value0),
        "convolution_curvature_1": cstr(value1),
        "reduced_curvature_0": cstr(reduced0),
        "reduced_curvature_1": cstr(reduced1),
        "ratio_curvature_1_to_corner_finite_part": cstr(value1 / finite),
        "curvature_zero": None if curvature_zero is None else cstr(curvature_zero),
        "abs_curvature_1": mp.nstr(abs(value1), 50),
    }


def evaluate_family(task: tuple[int, str, str]) -> list[dict]:
    n, beta_text, gamma_text = task
    mp.mp.dps = 90
    rho = mp.mpf(beta_text) + mp.j * mp.mpf(gamma_text)
    integrals = tuple(weighted_outer_integral(j, n, rho) for j in range(3))
    connection = forbidden_connection(n, rho)
    finite = corner_finite_part(n, rho)
    return [
        evaluate_case_from_data(n, rho, model, integrals, connection, finite)
        for model in ("reflected", "same", "opposite")
    ]


def precision_check_family(task: tuple[int, str, str]) -> list[dict]:
    n, beta_text, gamma_text = task
    rho = mp.mpf(beta_text) + mp.j * mp.mpf(gamma_text)
    values: dict[str, list[mp.mpc]] = {model: [] for model in ("reflected", "same", "opposite")}
    for dps in (60, 90):
        mp.mp.dps = dps
        integrals = tuple(weighted_outer_integral(j, n, rho) for j in range(3))
        connection = forbidden_connection(n, rho)
        for model in values:
            value, _ = convolution_from_integrals(
                n, rho, model, mp.mpf(1), integrals, connection
            )
            values[model].append(value)
    mp.mp.dps = 90
    output = []
    for model, pair in values.items():
        relative = abs(pair[1] - pair[0]) / max(mp.mpf(1), abs(pair[1]))
        output.append(
            {
                "n": n,
                "rho": cstr(rho),
                "charge_model": model,
                "dps60": cstr(pair[0]),
                "dps90": cstr(pair[1]),
                "relative_difference": mp.nstr(relative, 30),
            }
        )
    return output


def quadrature_check_task(task: tuple[int, str, str]) -> dict:
    n, beta_text, gamma_text = task
    mp.mp.dps = 90
    rho = mp.mpf(beta_text) + mp.j * mp.mpf(gamma_text)
    checks = []
    for j in range(3):
        via_hyper = weighted_outer_integral(j, n, rho)
        via_quad = weighted_outer_integral_quad(j, n, rho)
        rel = abs(via_hyper - via_quad) / max(mp.mpf(1), abs(via_hyper))
        checks.append(
            {
                "j": j,
                "hypergeometric": cstr(via_hyper),
                "quadrature": cstr(via_quad),
                "relative_difference": mp.nstr(rel, 30),
            }
        )
    return {"n": n, "rho": cstr(rho), "checks": checks}


def beta_scan_point(task: tuple[str, int]) -> list[dict]:
    height, idx = task
    mp.mp.dps = 90
    gamma = mp.mpf(height)
    beta = mp.mpf(idx) / 100
    rho = beta + mp.j * gamma
    integrals = tuple(weighted_outer_integral(j, 0, rho) for j in range(3))
    connection = forbidden_connection(0, rho)
    rows = []
    for model in ("reflected", "same", "opposite"):
        value, _ = convolution_from_integrals(
            0, rho, model, mp.mpf(1), integrals, connection
        )
        rows.append(
            {
                "height": height,
                "charge_model": model,
                "beta": mp.nstr(beta, 8),
                "value": cstr(value),
                "abs": mp.nstr(abs(value), 40),
            }
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="raw-results.json")
    parser.add_argument("--workers", type=int, default=min(32, os.cpu_count() or 1))
    args = parser.parse_args()
    started = time.time()
    mp.mp.dps = 90

    family_tasks = []
    for height in ZERO_HEIGHTS:
        for beta in ("0.2", "0.35", "0.5", "0.65", "0.8"):
            for n in (0, 1, 2):
                family_tasks.append((n, beta, height))

    representative_task = (0, "0.5", ZERO_HEIGHTS[0])
    beta_tasks = [(ZERO_HEIGHTS[0], idx) for idx in range(5, 96, 5)]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        case_families = list(pool.map(evaluate_family, family_tasks, chunksize=1))
        precision_families = list(
            pool.map(precision_check_family, [representative_task], chunksize=1)
        )
        quadrature_checks = list(
            pool.map(quadrature_check_task, [representative_task], chunksize=1)
        )
        beta_point_families = list(pool.map(beta_scan_point, beta_tasks, chunksize=1))

    cases = [case for family in case_families for case in family]
    precision_checks = [case for family in precision_families for case in family]
    beta_rows = [row for family in beta_point_families for row in family]
    beta_scans = []
    for model in ("reflected", "same", "opposite"):
        rows = [row for row in beta_rows if row["charge_model"] == model]
        minimum = min(rows, key=lambda row: mp.mpf(row["abs"]))
        beta_scans.append(
            {
                "height": ZERO_HEIGHTS[0],
                "charge_model": model,
                "rows": rows,
                "grid_minimum": minimum,
            }
        )
    output = {
        "purpose": "route-selection evidence only; forbidden in Lean proofs",
        "formula_version": "HC94-A.3-beta-3F2-v1",
        "python": platform.python_version(),
        "mpmath": mp.__version__,
        "precision_digits": mp.mp.dps,
        "workers": args.workers,
        "cases": cases,
        "precision_checks": precision_checks,
        "quadrature_checks": quadrature_checks,
        "beta_scans": beta_scans,
        "elapsed_seconds": None,
    }
    output["elapsed_seconds"] = time.time() - started
    target = Path(args.output)
    target.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    digest = hashlib.sha256(target.read_bytes()).hexdigest()
    print(json.dumps({"output": str(target), "sha256": digest, "elapsed_seconds": output["elapsed_seconds"]}))


if __name__ == "__main__":
    main()
