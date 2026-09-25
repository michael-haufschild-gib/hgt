#!/usr/bin/env python3
"""HCF route-selection computations derived from the Lean corpus.

Outputs are exploratory falsification/design evidence only.  They are never
proof premises and must not be imported into Lean.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import hashlib
import json
import math
import os
import platform
import time
from pathlib import Path
from typing import Any, Iterable

# Parallelism is across independent optimization/profile tasks.
for _name in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "NUMEXPR_NUM_THREADS",
):
    os.environ[_name] = "1"

import mpmath as mp
import numpy as np
import scipy
from scipy.optimize import brentq, differential_evolution, linprog, minimize_scalar


CORPUS_SOURCES = {
    "critical_feature_formula": (
        "formal/GaloisForLFunctions/RHTower/"
        "HedenmalmCriticalFeatureHolomorphicSectorCoercivity.lean:28"
    ),
    "three_center_receiver": (
        "formal/GaloisForLFunctions/RHTower/"
        "HedenmalmCriticalFeatureThreeCenterSharpQuantum.lean:330-339"
    ),
    "scalar_close_pair_no_go": (
        "formal/GaloisForLFunctions/RHTower/"
        "HedenmalmSubmicroscopicScalarDiagonalCovarianceNoGo.lean:25-101"
    ),
    "ward_damped_mask": (
        "formal/GaloisForLFunctions/RHTower/"
        "XiWardCubicPositiveShiftDampedDiagonalSeparator.lean:351-487"
    ),
    "entire_scalarization_no_go": (
        "formal/GaloisForLFunctions/RHTower/"
        "XiWardCubicPositiveShiftDampedDiagonalSeparatorNoGo.lean:25-57"
    ),
    "fixed_pole_pair_kernel": (
        "formal/GaloisForLFunctions/RHTower/"
        "XiEntireGaussianReflectionFibreCovariance.lean:328-415"
    ),
    "dzo_quartic": (
        "formal/GaloisForLFunctions/RHTower/"
        "DegreeZeroNonrealOffline.lean:21-37,222-285"
    ),
    "gamma_cell_mobility": (
        "formal/GaloisForLFunctions/RHTower/"
        "GammaCellNonrealMobility.lean:35-101"
    ),
}


def json_ready(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_ready(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_ready(v) for v in value]
    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, (np.floating, np.integer)):
        return value.item()
    return value


# ---------------------------------------------------------------------------
# Experiment 1: quantitative boundary of scalar submicroscopic separators


def transverse_kernel_matrix(d: np.ndarray, eps: np.ndarray) -> np.ndarray:
    """K_eps(d)=eps^2/(d^2+eps^2), one column per shift scale."""
    d2 = np.square(d[:, None])
    e2 = np.square(eps[None, :])
    return e2 / (d2 + e2)


def separator_lp_task(config: tuple[int, float, float, int]) -> dict[str, Any]:
    """Best stable signed mixture outside a prescribed resolution radius.

    Minimize sup K(d) over d>=d_min subject to K(0)=1 and an l1 coefficient
    budget.  The limit K(infinity)=0 forces objective t>=0.  A value near zero
    means the mixture is a numerical off-diagonal minorant only outside d_min;
    it says nothing at arbitrarily close collisions.
    """
    m, d_min, l1_budget, grid_size = config
    eps = np.power(2.0, np.linspace(-6.0, 6.0, m))
    d_max = 1.0e6
    grid = np.geomspace(d_min, d_max, grid_size)
    # Include all intrinsic scales and immediate neighborhoods.
    special = np.concatenate((eps, eps * (1.0 - 1e-8), eps * (1.0 + 1e-8)))
    grid = np.unique(np.concatenate((grid, special[special >= d_min])))
    kernel = transverse_kernel_matrix(grid, eps)

    # Variables are w_plus, w_minus, t, with w=w_plus-w_minus.
    nvar = 2 * m + 1
    objective = np.zeros(nvar)
    objective[-1] = 1.0
    aub = np.zeros((kernel.shape[0] + 1, nvar))
    aub[:-1, :m] = kernel
    aub[:-1, m : 2 * m] = -kernel
    aub[:-1, -1] = -1.0
    aub[-1, : 2 * m] = 1.0
    bub = np.zeros(kernel.shape[0] + 1)
    bub[-1] = l1_budget
    aeq = np.zeros((1, nvar))
    aeq[0, :m] = 1.0
    aeq[0, m : 2 * m] = -1.0
    beq = np.array([1.0])
    bounds = [(0.0, None)] * (2 * m) + [(0.0, None)]

    solved = linprog(
        objective,
        A_ub=aub,
        b_ub=bub,
        A_eq=aeq,
        b_eq=beq,
        bounds=bounds,
        method="highs",
        options={"presolve": True},
    )
    if not solved.success:
        return {
            "m": m,
            "d_min": d_min,
            "l1_budget": l1_budget,
            "success": False,
            "message": solved.message,
        }

    # The optimum t=0 is often highly degenerate.  Select the least-l1 witness
    # within numerical tolerance of the primary optimum; otherwise larger l1
    # budgets can return less stable witnesses despite containing smaller ones.
    lex_aub = np.vstack((aub, np.eye(1, nvar, nvar - 1)))
    lex_bub = np.concatenate((bub, [float(solved.fun) + 1.0e-10]))
    lex_objective = np.zeros(nvar)
    lex_objective[: 2 * m] = 1.0
    lex = linprog(
        lex_objective,
        A_ub=lex_aub,
        b_ub=lex_bub,
        A_eq=aeq,
        b_eq=beq,
        bounds=bounds,
        method="highs",
        options={"presolve": True},
    )
    if lex.success:
        selected = lex
    else:
        selected = solved

    w = selected.x[:m] - selected.x[m : 2 * m]
    # Independent denser validation, including the asymptotic endpoint 0.
    dense = np.geomspace(d_min, d_max * 100.0, 200_000)
    dense_values = transverse_kernel_matrix(dense, eps) @ w
    imax = int(np.argmax(dense_values))
    imin = int(np.argmin(dense_values))
    coefficient_l1 = float(np.sum(np.abs(w)))
    moment2 = float(np.dot(w, np.square(eps)))
    return {
        "m": m,
        "d_min": d_min,
        "l1_budget": l1_budget,
        "success": True,
        "lp_objective": float(solved.fun),
        "selected_grid_sup": float(selected.x[-1]),
        "lexicographic_l1_success": bool(lex.success),
        "validated_sup": float(max(0.0, dense_values[imax])),
        "validated_sup_location": float(dense[imax]),
        "validated_inf": float(dense_values[imin]),
        "validated_inf_location": float(dense[imin]),
        "coefficient_l1": coefficient_l1,
        "coefficient_l2": float(np.linalg.norm(w)),
        "asymptotic_second_moment": moment2,
        "eps": eps.tolist(),
        "weights": w.tolist(),
        "equality_residual": float(abs(np.sum(w) - 1.0)),
    }


def ward_anomaly(x: np.ndarray | float) -> np.ndarray | float:
    return (
        2.0 / np.power(2.0 * x + 2.0, 3)
        - 4.0 / np.power(3.0 * x + 1.5, 3)
        + 2.0 / np.power(4.0 * x + 1.0, 3)
    )


def ward_mask(x: np.ndarray | float) -> np.ndarray | float:
    return 1.0 - (108.0 / 115.0) * ward_anomaly(x)


def antisymmetric_cauchy_mask(x: np.ndarray | float, scale: float = 1.0) -> np.ndarray | float:
    x2 = np.square(x)
    return x2 / (x2 + scale * scale)


def mask_comparison() -> dict[str, Any]:
    grid = np.geomspace(1.0e-10, 1.0e10, 400_000)
    ward = ward_mask(grid)
    cauchy = antisymmetric_cauchy_mask(grid)
    delta = ward - cauchy

    fit = minimize_scalar(
        lambda log_scale: float(
            np.max(
                np.abs(
                    ward - antisymmetric_cauchy_mask(grid, math.exp(log_scale))
                )
            )
        ),
        bounds=(-8.0, 8.0),
        method="bounded",
        options={"xatol": 1e-12},
    )
    fitted_scale = math.exp(float(fit.x))

    levels: dict[str, dict[str, float]] = {}
    for level in (0.1, 0.25, 0.5, 0.75, 0.9, 0.99, 0.999):
        ward_x = brentq(lambda x: float(ward_mask(x) - level), 0.0, 1.0e6)
        cauchy_x = math.sqrt(level / (1.0 - level))
        levels[str(level)] = {"ward_x": ward_x, "cauchy_x": cauchy_x}

    pole_table: list[dict[str, float]] = []
    for k in range(1, 15):
        h = 10.0 ** (-k)
        for side in (-1.0, 1.0):
            d = 1.0 + side * h
            value = 1.0 / (1.0 - d * d)
            pole_table.append({"distance_to_pole": h, "side": side, "value": value})

    return {
        "ward_minus_unit_cauchy_min": float(np.min(delta)),
        "ward_minus_unit_cauchy_max": float(np.max(delta)),
        "ward_minus_unit_cauchy_argmin": float(grid[int(np.argmin(delta))]),
        "ward_minus_unit_cauchy_argmax": float(grid[int(np.argmax(delta))]),
        "best_uniform_cauchy_scale": fitted_scale,
        "best_uniform_cauchy_error": float(fit.fun),
        "level_crossings": levels,
        "meromorphic_real_shift_pole_table": pole_table,
    }


# ---------------------------------------------------------------------------
# Experiment 2: full infinite-lattice HCF receiver capacity


def lattice_resolvent_sum(a: np.ndarray | float, x: np.ndarray | float) -> np.ndarray | float:
    """sum_k 1/((x-k)^2+a^2), in closed form."""
    a = np.asarray(a)
    x = np.asarray(x)
    two_pi_a = 2.0 * np.pi * a
    return (
        np.pi
        / a
        * np.sinh(two_pi_a)
        / (np.cosh(two_pi_a) - np.cos(2.0 * np.pi * x))
    )


def hcf_lattice_energy(x: np.ndarray | float, y: np.ndarray | float) -> np.ndarray | float:
    """sum_k |2/(1+(x+iy-k)^2)|^2 for |y|<1/2."""
    x_arr = np.asarray(x, dtype=np.float64)
    y_arr = np.abs(np.asarray(y, dtype=np.float64))
    near = y_arr < 1.0e-7
    if np.ndim(y_arr) == 0:
        if float(y_arr) == 0.0:
            # Exact y=0 formula: -2 d/da lattice_resolvent_sum(a,x)|a=1.
            c = np.cos(2.0 * np.pi * x_arr)
            ch = np.cosh(2.0 * np.pi)
            sh = np.sinh(2.0 * np.pi)
            den = ch - c
            return 2.0 * np.pi * sh / den - 4.0 * np.pi**2 * (1.0 - ch * c) / den**2
        if float(y_arr) < 1.0e-4:
            # Avoid subtractive cancellation in S(1-y)-S(1+y).  This branch is
            # scalar and used only by the global optimizer near the axis.
            with mp.workdps(60):
                xx = mp.mpf(str(float(x_arr)))
                yy = mp.mpf(str(float(y_arr)))

                def _s(a: mp.mpf) -> mp.mpf:
                    return (
                        mp.pi
                        / a
                        * mp.sinh(2 * mp.pi * a)
                        / (mp.cosh(2 * mp.pi * a) - mp.cos(2 * mp.pi * xx))
                    )

                return float((_s(1 - yy) - _s(1 + yy)) / yy)
        return (
            lattice_resolvent_sum(1.0 - y_arr, x_arr)
            - lattice_resolvent_sum(1.0 + y_arr, x_arr)
        ) / y_arr
    result = np.empty(np.broadcast(x_arr, y_arr).shape, dtype=np.float64)
    xa, ya = np.broadcast_arrays(x_arr, y_arr)
    regular = ~near
    result[regular] = (
        lattice_resolvent_sum(1.0 - ya[regular], xa[regular])
        - lattice_resolvent_sum(1.0 + ya[regular], xa[regular])
    ) / ya[regular]
    c = np.cos(2.0 * np.pi * xa[near])
    ch = np.cosh(2.0 * np.pi)
    sh = np.sinh(2.0 * np.pi)
    den = ch - c
    result[near] = 2.0 * np.pi * sh / den - 4.0 * np.pi**2 * (1.0 - ch * c) / den**2
    return result


def lattice_y_task(y: float) -> dict[str, float]:
    solved = minimize_scalar(
        lambda x: float(hcf_lattice_energy(x, y)),
        bounds=(0.0, 0.5),
        method="bounded",
        options={"xatol": 1e-14, "maxiter": 1000},
    )
    candidates = [(float(solved.fun), float(solved.x))]
    for x in (0.0, 0.5):
        candidates.append((float(hcf_lattice_energy(x, y)), x))
    value, x = min(candidates)
    return {"y": y, "min_x": x, "min_energy": value}


def lattice_global_objective(v: np.ndarray) -> float:
    """Pickle-safe objective for SciPy's process-parallel global optimizer."""
    return float(hcf_lattice_energy(v[0], v[1]))


def direct_lattice_sum(x: float, y: float, radius: int, chunk: int = 1_000_000) -> float:
    total = 0.0
    for start in range(-radius, radius + 1, chunk):
        stop = min(radius + 1, start + chunk)
        k = np.arange(start, stop, dtype=np.float64)
        u = x - k
        den = np.square(1.0 + np.square(u) - y * y) + np.square(2.0 * u * y)
        total += float(np.sum(4.0 / den, dtype=np.float64))
    return total


def lattice_capacity(workers: int, quick: bool) -> tuple[dict[str, Any], list[dict[str, float]]]:
    y_count = 129 if quick else 2049
    y_values = np.linspace(0.0, 0.499999999, y_count)
    with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
        profile = list(pool.map(lattice_y_task, y_values, chunksize=4))

    de = differential_evolution(
        lattice_global_objective,
        bounds=((0.0, 0.5), (0.0, 0.499999999)),
        seed=20260828,
        tol=1e-12,
        atol=1e-13,
        popsize=48 if not quick else 16,
        maxiter=1200 if not quick else 200,
        polish=True,
        workers=workers,
        updating="deferred",
    )
    best_profile = min(profile, key=lambda row: row["min_energy"])

    mp.mp.dps = 120
    pi = mp.pi
    exact_candidate = 2 * pi * mp.tanh(pi) - 2 * pi**2 / mp.cosh(pi) ** 2
    candidate_float = float(exact_candidate)
    direct_radius = 100_000 if quick else 5_000_000
    direct = direct_lattice_sum(0.5, 0.0, direct_radius)
    tail_upper = 8.0 / (3.0 * max(1.0, direct_radius - 0.5) ** 3)

    # Formula/direct-sum cross-check away from the candidate minimum.
    rng = np.random.default_rng(20260828)
    spot_errors: list[float] = []
    for _ in range(64 if quick else 512):
        x = float(rng.random() * 0.5)
        y = float(rng.random() * 0.499)
        closed = float(hcf_lattice_energy(x, y))
        direct_spot = direct_lattice_sum(x, y, 20_000)
        spot_errors.append(abs(closed - direct_spot))

    h = 1e-4
    e00 = float(hcf_lattice_energy(0.5, 0.0))
    hxx = (
        float(hcf_lattice_energy(0.5 + h, 0.0))
        - 2.0 * e00
        + float(hcf_lattice_energy(0.5 - h, 0.0))
    ) / h**2
    hyy = 2.0 * (float(hcf_lattice_energy(0.5, h)) - e00) / h**2

    result = {
        "global_optimizer": {
            "x": float(de.x[0]),
            "y": float(de.x[1]),
            "energy": float(de.fun),
            "iterations": int(de.nit),
            "evaluations": int(de.nfev),
            "success": bool(de.success),
            "message": str(de.message),
        },
        "best_y_profile": best_profile,
        "candidate": {
            "x": 0.5,
            "y": 0.0,
            "closed_form": "2*pi*tanh(pi) - 2*pi^2*sech(pi)^2",
            "value_120dps": mp.nstr(exact_candidate, 115),
            "value_float": candidate_float,
            "receiver_budget_threshold_div_16": candidate_float / 16.0,
            "three_center_budget_threshold": 1452.0 / 4225.0,
            "threshold_gain": candidate_float / 16.0 - 1452.0 / 4225.0,
        },
        "direct_sum_check": {
            "radius": direct_radius,
            "value": direct,
            "absolute_difference": abs(direct - candidate_float),
            "tail_upper_bound": tail_upper,
        },
        "spot_check": {
            "count": len(spot_errors),
            "max_absolute_difference_radius_20000": max(spot_errors),
            "mean_absolute_difference_radius_20000": float(np.mean(spot_errors)),
        },
        "numerical_hessian_diagonal": {"xx": hxx, "yy": hyy},
        "axis_range": {
            "min": float(min(row["min_energy"] for row in profile)),
            "max": float(max(row["min_energy"] for row in profile)),
        },
    }
    return result, profile


# ---------------------------------------------------------------------------
# Experiment 3: explicit gamma-cell mobility stress test


def dzo_chunk_task(config: tuple[int, int]) -> tuple[int, int, float]:
    start, stop = config
    idx = np.arange(start, stop, dtype=np.longdouble)
    tau = (2.0 * idx + 1.0) * np.longdouble(str(math.pi)) / (
        8.0 * np.log(np.longdouble(2.0))
    )
    x = np.asarray(np.remainder(tau, np.longdouble(1.0)), dtype=np.float64)
    values = hcf_lattice_energy(x, 1.0 / 8.0)
    return start, stop, float(np.sum(values, dtype=np.float64))


def dzo_count_positive(T: float) -> int:
    bound = (8.0 * math.log(2.0) * T / math.pi - 1.0) / 2.0
    return max(0, math.floor(bound) + 1)


def riemann_zero_count_main(T: float) -> float:
    return T / (2.0 * math.pi) * (math.log(T / (2.0 * math.pi)) - 1.0) + 7.0 / 8.0


def mobility_stress(workers: int, quick: bool) -> dict[str, Any]:
    t_values = [1e2, 1e3, 1e4, 1e5]
    if not quick:
        t_values += [1e6, 1e7, 1e8]
    chunk_size = 100_000 if quick else 1_000_000
    tasks: list[tuple[float, tuple[int, int]]] = []
    for T in t_values:
        count = dzo_count_positive(T)
        for start in range(0, count, chunk_size):
            tasks.append((T, (start, min(count, start + chunk_size))))

    sums = {T: 0.0 for T in t_values}
    with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
        future_to_t = {
            pool.submit(dzo_chunk_task, chunk): T for T, chunk in tasks
        }
        for future in concurrent.futures.as_completed(future_to_t):
            T = future_to_t[future]
            _start, _stop, value = future.result()
            sums[T] += value

    average_prediction = 128.0 * math.pi / 63.0
    rows: list[dict[str, Any]] = []
    for T in t_values:
        seq_count = dzo_count_positive(T)
        dzo_zeros = 2 * seq_count  # roots -1/32 and -1/8 at each positive ordinate
        added_energy = 2.0 * sums[T]
        nmain = riemann_zero_count_main(T)
        ratio = dzo_zeros / nmain
        rows.append(
            {
                "T": T,
                "one_root_ordinate_count": seq_count,
                "dzo_offline_zero_count": dzo_zeros,
                "riemann_main_count": nmain,
                "offline_to_riemann_main_ratio": ratio,
                "proxy_offline_fraction_zeta_times_dzo": dzo_zeros / (nmain + dzo_zeros),
                "power_needed_for_25pct_proxy_offline_fraction": max(
                    1, math.ceil(nmain / (3.0 * dzo_zeros))
                ),
                "added_full_lattice_hermitian_energy": added_energy,
                "mean_energy_per_dzo_zero": added_energy / dzo_zeros,
                "mean_energy_minus_equimeasure_prediction": (
                    added_energy / dzo_zeros - average_prediction
                ),
                "ratio_times_log_T": ratio * math.log(T),
            }
        )

    density = 8.0 * math.log(2.0) / math.pi

    def asymptotic_fraction(log_t: float) -> float:
        T = math.exp(log_t)
        nd = density * T
        nmain = riemann_zero_count_main(T)
        return nd / (nd + nmain)

    crossover_log = brentq(
        lambda log_t: asymptotic_fraction(log_t) - 0.25,
        math.log(1e3),
        math.log(1e30),
    )
    return {
        "zero_sequences": {
            "ordinary_s_real_parts": [3.0 / 8.0, 5.0 / 8.0],
            "centered_z_imaginary_parts": [-1.0 / 8.0, 1.0 / 8.0],
            "positive_ordinate_formula": "(2*n+1)*pi/(8*log(2))",
            "combined_positive_zero_density_per_height": density,
        },
        "equimeasure_mean_energy_per_zero": average_prediction,
        "asymptotic_offline_to_riemann_main_ratio_times_log_T": 16.0 * math.log(2.0),
        "asymptotic_25pct_proxy_fraction_crossover_T": math.exp(crossover_log),
        "rows": rows,
    }


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def write_csv(path: Path, rows: Iterable[dict[str, Any]]) -> None:
    rows = list(rows)
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, default=Path("results"))
    parser.add_argument("--workers", type=int, default=max(1, min(64, os.cpu_count() or 1)))
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    started = time.time()

    dmins = np.geomspace(1.0e-6, 10.0, 7 if args.quick else 15)
    budgets = [1.0, 4.0, 16.0, 64.0] if args.quick else [
        1.0,
        2.0,
        4.0,
        8.0,
        16.0,
        32.0,
        64.0,
        128.0,
        256.0,
    ]
    dimensions = [7] if args.quick else [7, 11, 15]
    lp_grid_size = 500 if args.quick else 2200
    lp_configs = [
        (m, float(dmin), budget, lp_grid_size)
        for m in dimensions
        for dmin in dmins
        for budget in budgets
    ]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        separator_rows = list(pool.map(separator_lp_task, lp_configs, chunksize=1))
    separator_rows.sort(key=lambda r: (r["m"], r["d_min"], r["l1_budget"]))
    write_csv(
        args.output_dir / "separator_phase.csv",
        [
            {k: v for k, v in row.items() if k not in {"eps", "weights"}}
            for row in separator_rows
        ],
    )

    mask = mask_comparison()
    lattice, lattice_profile = lattice_capacity(args.workers, args.quick)
    write_csv(args.output_dir / "lattice_y_profile.csv", lattice_profile)
    mobility = mobility_stress(args.workers, args.quick)
    write_csv(args.output_dir / "mobility_height_profile.csv", mobility["rows"])

    successful = [row for row in separator_rows if row.get("success")]
    separator_summary = {
        "configuration_count": len(separator_rows),
        "successful_count": len(successful),
        "near_minorant_count_validated_sup_le_1e-8": sum(
            row["validated_sup"] <= 1e-8 for row in successful
        ),
        "resolution_boundary_by_dimension_and_budget": [],
        "mask_comparison": mask,
    }
    for m in dimensions:
        for budget in budgets:
            candidates = [
                row
                for row in successful
                if row["m"] == m and row["l1_budget"] == budget
            ]
            if candidates:
                feasible = [row for row in candidates if row["validated_sup"] <= 1e-8]
                boundary = min(feasible, key=lambda row: row["d_min"]) if feasible else None
                separator_summary["resolution_boundary_by_dimension_and_budget"].append(
                    {
                        "m": m,
                        "l1_budget": budget,
                        "smallest_sampled_d_min_with_sup_le_1e-8": (
                            boundary["d_min"] if boundary is not None else None
                        ),
                        "boundary_row": boundary,
                        "lowest_validated_sup_row": min(
                            candidates, key=lambda row: row["validated_sup"]
                        ),
                    }
                )

    result = {
        "status": "COMPUTATIONAL_ROUTE_SELECTION_ONLY_NOT_PROOF",
        "corpus_sources": CORPUS_SOURCES,
        "run": {
            "quick": args.quick,
            "workers": args.workers,
            "elapsed_seconds": time.time() - started,
            "python": platform.python_version(),
            "platform": platform.platform(),
            "numpy": np.__version__,
            "scipy": scipy.__version__,
            "mpmath": mp.__version__,
            "cpu_count": os.cpu_count(),
        },
        "separator": separator_summary,
        "lattice_capacity": lattice,
        "gamma_cell_mobility": mobility,
    }
    result_path = args.output_dir / "results.json"
    result_path.write_text(json.dumps(json_ready(result), indent=2) + "\n", encoding="utf-8")

    files = [
        result_path,
        args.output_dir / "separator_phase.csv",
        args.output_dir / "lattice_y_profile.csv",
        args.output_dir / "mobility_height_profile.csv",
    ]
    checksums = args.output_dir / "SHA256SUMS"
    checksums.write_text(
        "".join(f"{sha256(path)}  {path.name}\n" for path in files),
        encoding="utf-8",
    )
    print(json.dumps(json_ready(result["run"]), indent=2))


if __name__ == "__main__":
    main()
