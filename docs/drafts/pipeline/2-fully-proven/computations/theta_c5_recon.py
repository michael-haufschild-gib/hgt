#!/usr/bin/env python3
"""Computational reconnaissance for completed-theta cumulative C5 balance.

Research use only.  Outputs may kill or sharpen routes but are not proof inputs and
must never be imported into Lean.  Formula source is the local HGT Lean corpus:

  thetaCuspSeed t = 2*pi*(2*pi*t^4 - 3*t^2)*exp(-pi*t^2)
  thetaCuspFullSource x = sum_n exp(x/2)*thetaCuspSeed(n*exp(x))

Evenness of the completed source is used to evaluate only nonnegative arguments.
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import csv
import json
import math
import os
import platform
import socket
import time
from pathlib import Path
from typing import Any, Iterable

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import mpmath as mp
import numpy as np
import sympy as sp


Q_EDGES = np.array(
    [1e-3, 1e-2, 1e-1, 1.0, 10.0, 100.0, np.inf],
    dtype=np.float64,
)


def _atom_log_scores(z: np.ndarray, n_values: np.ndarray) -> tuple[np.ndarray, ...]:
    """Return log atom and first three log-derivative scores at z >= 0."""
    zz = z[None, :]
    nn = n_values[:, None]
    s = np.pi * nn * nn * np.exp(2.0 * zz)
    d = 2.0 * s - 3.0
    log_t = math.log(2.0) + 0.5 * zz + np.log(s) + np.log(d) - s
    g1 = 2.5 + 4.0 * s / d - 2.0 * s
    g2 = -4.0 * s - 24.0 * s / (d * d)
    g3 = -8.0 * s + 48.0 * s * (2.0 * s + 3.0) / (d * d * d)
    return log_t, g1, g2, g3


def _logjets_from_terms(
    x: np.ndarray,
    n_values: np.ndarray,
    log_coefficients: np.ndarray | None = None,
) -> tuple[np.ndarray, ...]:
    """Log source and its first three derivatives, using completed-source evenness."""
    z = np.abs(x)
    log_t, g1, g2, g3 = _atom_log_scores(z, n_values)
    if log_coefficients is not None:
        log_t = log_t + log_coefficients
    max_log = np.max(log_t, axis=0)
    weights = np.exp(log_t - max_log[None, :])
    mass = np.sum(weights, axis=0)
    probs = weights / mass[None, :]
    log_f = max_log + np.log(mass)

    f1 = np.sum(probs * g1, axis=0)
    centered_g1 = g1 - f1[None, :]
    ell2 = np.sum(probs * (g2 + centered_g1 * centered_g1), axis=0)
    ell3 = np.sum(
        probs * (g3 + 3.0 * centered_g1 * g2 + centered_g1**3), axis=0
    )

    sign = np.sign(x)
    return log_f, sign * f1, ell2, sign * ell3


def _reciprocal_expm1(q: np.ndarray) -> np.ndarray:
    result = np.empty_like(q)
    direct = q < 50.0
    result[direct] = 1.0 / np.expm1(q[direct])
    result[~direct] = np.exp(-q[~direct])
    return result


def actual_logjets(x: np.ndarray, nmax: int) -> tuple[np.ndarray, ...]:
    return _logjets_from_terms(x, np.arange(1, nmax + 1, dtype=np.float64))


def _balance_from_reflected_jets(
    u: np.ndarray,
    t: np.ndarray,
    center: tuple[np.ndarray, ...],
    plus: tuple[np.ndarray, ...],
    minus: tuple[np.ndarray, ...],
) -> dict[str, np.ndarray]:
    l0, _l01, l02, _l03 = center
    la, la1, la2, la3 = plus
    lb, lb1, lb2, lb3 = minus
    q = 2.0 * l0 - la - lb
    q1 = lb1 - la1
    q2 = -la2 - lb2
    q3 = lb3 - la3

    with np.errstate(over="ignore", divide="ignore", invalid="ignore", under="ignore"):
        rho = _reciprocal_expm1(q)
        m = 0.5 * t * q1 * rho
        elasticity_numerator = t * (q2 - q1 * q1) - q1
        e = elasticity_numerator / (2.0 * q1)
        me = 0.25 * t * rho * elasticity_numerator
        balance = 6.0 - 2.0 * m - 4.0 * m * m + 5.0 * me
        riccati = 2.0 * q1 * q2 - q3
    return {
        "q": q,
        "q1": q1,
        "q2": q2,
        "q3": q3,
        "m": m,
        "e": e,
        "balance": balance,
        "riccati": riccati,
        "ell2_center": l02,
        "ell2_plus": la2,
        "ell2_minus": lb2,
    }


def actual_balance_batch(u: np.ndarray, t: np.ndarray, nmax: int) -> dict[str, np.ndarray]:
    center = actual_logjets(u, nmax)
    plus = actual_logjets(u + t, nmax)
    minus = actual_logjets(u - t, nmax)
    values = _balance_from_reflected_jets(
        u,
        t,
        center,
        plus,
        minus,
    )
    # In the large-center boundary layer t ~ exp(-u), subtracting three log
    # sources of size exp(2u) destroys q and q1 in float64.  Above u=8 the
    # n=1 atom dominates beyond float64 resolution, so use exact stable n=1
    # second-difference identities.  High-precision checks remain independent.
    stable = (u > 1.0) & (t < u)
    if np.any(stable):
        us = u[stable]
        ts = t[stable]
        s0 = np.pi * np.exp(2.0 * us)
        sinh_t = np.sinh(ts)
        sinh_2t = np.sinh(2.0 * ts)
        sa = s0 * np.exp(2.0 * ts)
        sb = s0 * np.exp(-2.0 * ts)
        da = 2.0 * sa - 3.0
        db = 2.0 * sb - 3.0
        q = 4.0 * s0 * sinh_t * sinh_t + np.log1p(
            24.0 * s0 * sinh_t * sinh_t / (da * db)
        )
        q1 = 4.0 * s0 * sinh_2t * (1.0 + 6.0 / (da * db))
        q2 = -plus[2][stable] - minus[2][stable]
        q3 = minus[3][stable] - plus[3][stable]
        rho = _reciprocal_expm1(q)
        m = 0.5 * ts * q1 * rho
        en = ts * (q2 - q1 * q1) - q1
        e = en / (2.0 * q1)
        me = 0.25 * ts * rho * en
        values["q"][stable] = q
        values["q1"][stable] = q1
        values["q2"][stable] = q2
        values["q3"][stable] = q3
        values["m"][stable] = m
        values["e"][stable] = e
        values["balance"][stable] = 6.0 - 2.0 * m - 4.0 * m * m + 5.0 * me
        values["riccati"][stable] = 2.0 * q1 * q2 - q3
    return values


def _row_from_index(
    i: int,
    u: np.ndarray,
    t: np.ndarray,
    family: np.ndarray,
    values: dict[str, np.ndarray],
) -> dict[str, float | int]:
    return {
        "u": float(u[i]),
        "t": float(t[i]),
        "family": int(family[i]),
        "q": float(values["q"][i]),
        "q1": float(values["q1"][i]),
        "q2": float(values["q2"][i]),
        "m": float(values["m"][i]),
        "e": float(values["e"][i]),
        "balance": float(values["balance"][i]),
        "riccati": float(values["riccati"][i]),
    }


def _merge_top(rows: list[dict[str, Any]], new_rows: Iterable[dict[str, Any]], k: int) -> None:
    rows.extend(new_rows)
    rows.sort(key=lambda row: row["balance"])
    del rows[k:]


def _actual_worker(args: tuple[int, int, int, int, int]) -> dict[str, Any]:
    worker_id, sample_count, chunk_size, nmax, top_k = args
    rng = np.random.default_rng(0xC5A11 + 104729 * worker_id)
    top: list[dict[str, Any]] = []
    bin_top: list[dict[str, Any] | None] = [None] * (len(Q_EDGES) - 1)
    total_valid = 0
    negative_count = 0
    negative_elasticity_count = 0

    for start in range(0, sample_count, chunk_size):
        size = min(chunk_size, sample_count - start)
        family = rng.integers(0, 4, size=size, dtype=np.int8)
        u = np.empty(size, dtype=np.float64)
        t = np.empty(size, dtype=np.float64)

        mask = family == 0
        u[mask] = rng.uniform(0.0, 14.0, np.count_nonzero(mask))
        t[mask] = np.exp(rng.uniform(math.log(1e-8), math.log(24.0), np.count_nonzero(mask)))

        mask = family == 1
        u[mask] = rng.uniform(0.0, 22.0, np.count_nonzero(mask))
        w = np.exp(rng.uniform(math.log(2e-5), math.log(30.0), np.count_nonzero(mask)))
        t[mask] = w * np.exp(-u[mask])

        mask = family == 2
        u[mask] = np.exp(rng.uniform(math.log(1e-3), math.log(20.0), np.count_nonzero(mask)))
        ratio = rng.uniform(1e-7, 1.0 - 1e-7, np.count_nonzero(mask))
        t[mask] = ratio * u[mask]

        mask = family == 3
        u[mask] = rng.uniform(0.0, 14.0, np.count_nonzero(mask))
        delta = np.exp(rng.uniform(math.log(1e-7), math.log(12.0), np.count_nonzero(mask)))
        delta *= rng.choice(np.array([-1.0, 1.0]), np.count_nonzero(mask))
        t[mask] = np.abs(u[mask] + delta)
        t[mask] = np.maximum(t[mask], 1e-10)

        values = actual_balance_batch(u, t, nmax)
        valid = (
            np.isfinite(values["balance"])
            & (values["q"] >= Q_EDGES[0])
            & (values["q1"] > 0.0)
            & (values["m"] > 0.0)
            & (values["m"] <= 1.0000001)
        )
        indices = np.flatnonzero(valid)
        total_valid += int(indices.size)
        if indices.size == 0:
            continue
        negative_count += int(np.count_nonzero(values["balance"][indices] < -1e-10))
        negative_elasticity_count += int(np.count_nonzero(values["e"][indices] < 0.0))

        local_k = min(top_k, indices.size)
        chosen = indices[np.argpartition(values["balance"][indices], local_k - 1)[:local_k]]
        _merge_top(
            top,
            (_row_from_index(int(i), u, t, family, values) for i in chosen),
            top_k,
        )

        bins = np.searchsorted(Q_EDGES, values["q"][indices], side="right") - 1
        for b in np.unique(bins):
            if b < 0 or b >= len(bin_top):
                continue
            candidates = indices[bins == b]
            j = int(candidates[np.argmin(values["balance"][candidates])])
            row = _row_from_index(j, u, t, family, values)
            if bin_top[b] is None or row["balance"] < bin_top[b]["balance"]:
                bin_top[b] = row

    return {
        "top": top,
        "bin_top": bin_top,
        "valid": total_valid,
        "negative": negative_count,
        "negative_elasticity": negative_elasticity_count,
    }


def _mixture_logjets(
    x: np.ndarray,
    n_values: np.ndarray,
    log_coefficients: np.ndarray,
) -> tuple[np.ndarray, ...]:
    return _logjets_from_terms(x, n_values, log_coefficients)


def _mixture_worker(args: tuple[int, int, int, int, int]) -> dict[str, Any]:
    worker_id, sample_count, chunk_size, top_k, atom_count = args
    rng = np.random.default_rng(0xA70C5 + 130363 * worker_id + 15485863 * atom_count)
    n_values = np.arange(1, atom_count + 1, dtype=np.float64)
    top: list[dict[str, Any]] = []
    total_filtered = 0
    negative_count = 0
    most_balanced_negative: dict[str, Any] | None = None
    smallest_coefficient_spread_negative: dict[str, Any] | None = None

    for start in range(0, sample_count, chunk_size):
        size = min(chunk_size, sample_count - start)
        u = np.exp(rng.uniform(math.log(1e-3), math.log(3.0), size))
        ratio = rng.uniform(1e-5, 1.0 - 1e-5, size)
        t = ratio * u

        logits = rng.normal(0.0, 4.0, size=(atom_count, size))
        logits -= np.max(logits, axis=0, keepdims=True)
        probs = np.exp(logits)
        probs /= np.sum(probs, axis=0, keepdims=True)

        center_atom_logs = _atom_log_scores(u, n_values)[0]
        log_coefficients = np.log(probs) - center_atom_logs
        center = _mixture_logjets(u, n_values, log_coefficients)
        plus = _mixture_logjets(u + t, n_values, log_coefficients)
        minus = _mixture_logjets(u - t, n_values, log_coefficients)
        values = _balance_from_reflected_jets(u, t, center, plus, minus)

        valid = (
            np.isfinite(values["balance"])
            & (values["q"] >= Q_EDGES[0])
            & (values["q1"] > 0.0)
            & (values["q2"] > 0.0)
            & (values["m"] > 0.0)
            & (values["m"] <= 1.0000001)
            & (values["ell2_center"] < 0.0)
            & (values["ell2_plus"] < 0.0)
            & (values["ell2_minus"] < 0.0)
            & (values["riccati"] >= 0.0)
        )
        indices = np.flatnonzero(valid)
        total_filtered += int(indices.size)
        if indices.size == 0:
            continue
        negative_count += int(np.count_nonzero(values["balance"][indices] < -1e-10))
        local_k = min(top_k, indices.size)
        chosen = indices[np.argpartition(values["balance"][indices], local_k - 1)[:local_k]]
        rows = []
        for i_raw in chosen:
            i = int(i_raw)
            row = _row_from_index(i, u, t, np.full(size, atom_count, dtype=np.int8), values)
            row["atom_count"] = atom_count
            row["center_probabilities"] = [float(probs[j, i]) for j in range(atom_count)]
            row["log_coefficients"] = [float(log_coefficients[j, i]) for j in range(atom_count)]
            row["ratio"] = float(ratio[i])
            rows.append(row)
        _merge_top(top, rows, top_k)

        negative_indices = indices[values["balance"][indices] < -1e-8]
        if negative_indices.size:
            min_probabilities = np.min(probs[:, negative_indices], axis=0)
            balanced_i = int(negative_indices[np.argmax(min_probabilities)])
            coefficient_spreads = (
                np.max(log_coefficients[:, negative_indices], axis=0)
                - np.min(log_coefficients[:, negative_indices], axis=0)
            )
            spread_i = int(negative_indices[np.argmin(coefficient_spreads)])
            for i, kind in ((balanced_i, "balanced"), (spread_i, "spread")):
                row = _row_from_index(i, u, t, np.full(size, atom_count, dtype=np.int8), values)
                row["atom_count"] = atom_count
                row["center_probabilities"] = [float(probs[j, i]) for j in range(atom_count)]
                row["log_coefficients"] = [float(log_coefficients[j, i]) for j in range(atom_count)]
                row["ratio"] = float(ratio[i])
                row["minimum_center_probability"] = float(np.min(probs[:, i]))
                row["coefficient_log_spread"] = float(
                    np.max(log_coefficients[:, i]) - np.min(log_coefficients[:, i])
                )
                if kind == "balanced":
                    if (
                        most_balanced_negative is None
                        or row["minimum_center_probability"]
                        > most_balanced_negative["minimum_center_probability"]
                    ):
                        most_balanced_negative = row
                elif (
                    smallest_coefficient_spread_negative is None
                    or row["coefficient_log_spread"]
                    < smallest_coefficient_spread_negative["coefficient_log_spread"]
                ):
                    smallest_coefficient_spread_negative = row

    return {
        "top": top,
        "filtered": total_filtered,
        "negative": negative_count,
        "most_balanced_negative": most_balanced_negative,
        "smallest_coefficient_spread_negative": smallest_coefficient_spread_negative,
    }


def _run_workers(
    fn: Any,
    total_samples: int,
    workers: int,
    extra: tuple[Any, ...],
) -> list[dict[str, Any]]:
    base = total_samples // workers
    remainder = total_samples % workers
    jobs = [
        (i, base + (1 if i < remainder else 0), *extra)
        for i in range(workers)
    ]
    with cf.ProcessPoolExecutor(max_workers=workers) as executor:
        return list(executor.map(fn, jobs))


def _aggregate_actual(parts: list[dict[str, Any]], top_k: int) -> dict[str, Any]:
    top: list[dict[str, Any]] = []
    bins: list[dict[str, Any] | None] = [None] * (len(Q_EDGES) - 1)
    for part in parts:
        _merge_top(top, part["top"], top_k)
        for i, row in enumerate(part["bin_top"]):
            if row is not None and (bins[i] is None or row["balance"] < bins[i]["balance"]):
                bins[i] = row
    return {
        "valid": sum(part["valid"] for part in parts),
        "negative": sum(part["negative"] for part in parts),
        "negative_elasticity": sum(part["negative_elasticity"] for part in parts),
        "top": top,
        "q_bin_minima": [
            {
                "q_interval": [float(Q_EDGES[i]), float(Q_EDGES[i + 1])],
                "minimum": bins[i],
            }
            for i in range(len(bins))
        ],
    }


def _aggregate_mixture(parts: list[dict[str, Any]], top_k: int) -> dict[str, Any]:
    top: list[dict[str, Any]] = []
    for part in parts:
        _merge_top(top, part["top"], top_k)
    balanced = [part["most_balanced_negative"] for part in parts if part["most_balanced_negative"]]
    smallest_spread = [
        part["smallest_coefficient_spread_negative"]
        for part in parts
        if part["smallest_coefficient_spread_negative"]
    ]
    return {
        "filtered": sum(part["filtered"] for part in parts),
        "negative": sum(part["negative"] for part in parts),
        "top": top,
        "most_balanced_negative": max(
            balanced, key=lambda row: row["minimum_center_probability"], default=None
        ),
        "smallest_coefficient_spread_negative": min(
            smallest_spread, key=lambda row: row["coefficient_log_spread"], default=None
        ),
    }


def _mp_atom_log_scores(z: mp.mpf, n: int) -> tuple[mp.mpf, ...]:
    s = mp.pi * n * n * mp.exp(2 * z)
    d = 2 * s - 3
    log_t = mp.log(2) + z / 2 + mp.log(s) + mp.log(d) - s
    g1 = mp.mpf("2.5") + 4 * s / d - 2 * s
    g2 = -4 * s - 24 * s / (d * d)
    g3 = -8 * s + 48 * s * (2 * s + 3) / (d * d * d)
    return log_t, g1, g2, g3


def _mp_logjets(x: mp.mpf, log_coefficients: list[mp.mpf] | None = None) -> tuple[mp.mpf, ...]:
    z = abs(x)
    count = len(log_coefficients) if log_coefficients is not None else 64
    atoms = []
    for n in range(1, count + 1):
        row = list(_mp_atom_log_scores(z, n))
        if log_coefficients is not None:
            row[0] += log_coefficients[n - 1]
        atoms.append(row)
        if log_coefficients is None and n >= 8 and row[0] - atoms[0][0] < -mp.mp.dps * mp.log(10) - 30:
            break
    maximum = max(row[0] for row in atoms)
    weights = [mp.exp(row[0] - maximum) for row in atoms]
    mass = mp.fsum(weights)
    probs = [weight / mass for weight in weights]
    f1 = mp.fsum(p * row[1] for p, row in zip(probs, atoms))
    ell2 = mp.fsum(p * (row[2] + (row[1] - f1) ** 2) for p, row in zip(probs, atoms))
    ell3 = mp.fsum(
        p * (row[3] + 3 * (row[1] - f1) * row[2] + (row[1] - f1) ** 3)
        for p, row in zip(probs, atoms)
    )
    sign = mp.sign(x)
    return maximum + mp.log(mass), sign * f1, ell2, sign * ell3


def _mp_balance(u: float, t: float, log_coefficients: list[float] | None = None) -> dict[str, str]:
    uu = mp.mpf(str(u))
    tt = mp.mpf(str(t))
    coeffs = None if log_coefficients is None else [mp.mpf(str(x)) for x in log_coefficients]
    l0 = _mp_logjets(uu, coeffs)
    la = _mp_logjets(uu + tt, coeffs)
    lb = _mp_logjets(uu - tt, coeffs)
    q = 2 * l0[0] - la[0] - lb[0]
    q1 = lb[1] - la[1]
    q2 = -la[2] - lb[2]
    q3 = lb[3] - la[3]
    rho = 1 / mp.expm1(q)
    m = tt * q1 * rho / 2
    e = (tt * (q2 - q1**2) - q1) / (2 * q1)
    balance = 6 - 2 * m - 4 * m**2 + 5 * m * e
    return {
        "u": mp.nstr(uu, 30),
        "t": mp.nstr(tt, 30),
        "q": mp.nstr(q, 50),
        "q1": mp.nstr(q1, 50),
        "q2": mp.nstr(q2, 50),
        "m": mp.nstr(m, 50),
        "e": mp.nstr(e, 50),
        "balance": mp.nstr(balance, 60),
        "riccati": mp.nstr(2 * q1 * q2 - q3, 50),
    }


def _high_precision_checks(rows: list[dict[str, Any]], mixture: bool = False) -> list[dict[str, str]]:
    checks = []
    for row in rows:
        coefficients = row.get("log_coefficients") if mixture else None
        checks.append(_mp_balance(row["u"], row["t"], coefficients))
    return checks


def _dominant_atom_profile() -> dict[str, Any]:
    def profile(q: mp.mpf) -> mp.mpf:
        m = q / mp.expm1(q)
        return 6 - (2 + 5 * q) * m - 4 * m * m

    thresholds = [mp.mpf("1e-10"), mp.mpf("1e-8"), mp.mpf("1e-6"), mp.mpf("1e-4"),
                  mp.mpf("1e-2"), mp.mpf("1e-1"), mp.mpf("1")]
    grid = [mp.power(10, -10 + 16 * i / 200000) for i in range(200001)]
    values = [profile(q) for q in grid]
    minima = []
    for threshold in thresholds:
        candidates = [(v, q) for v, q in zip(values, grid) if q >= threshold]
        value, q = min(candidates, key=lambda pair: pair[0])
        minima.append({"q_min": mp.nstr(threshold, 12), "q": mp.nstr(q, 30), "balance": mp.nstr(value, 50)})
    return {"sampled_negative": sum(1 for value in values if value < 0), "threshold_minima": minima}


def _high_precision_boundary_layer_scan() -> dict[str, Any]:
    """Resolve q below float64 search floor in center-adapted coordinates."""
    u_values = [mp.mpf(i) / 100 for i in range(101)]
    u_values += [mp.mpf(1) + mp.mpf(21 * i) / 210 for i in range(1, 211)]
    w_values = [mp.mpf(x) for x in ("1e-5", "3e-5", "1e-4", "3e-4", "1e-3", "3e-3", "1e-2")]
    minimum: dict[str, str] | None = None
    minimum_value: mp.mpf | None = None
    minimum_ratio: dict[str, str] | None = None
    minimum_ratio_value: mp.mpf | None = None
    negative = 0
    evaluated = 0
    for u in u_values:
        for w in w_values:
            t = w * mp.exp(-u)
            row = _mp_balance(float(u), float(t))
            q = mp.mpf(row["q"])
            value = mp.mpf(row["balance"])
            if q <= 0:
                continue
            evaluated += 1
            if value < 0:
                negative += 1
            if minimum_value is None or value < minimum_value:
                minimum_value = value
                minimum = row
                minimum["w=t*exp(u)"] = mp.nstr(w, 30)
            if q <= mp.mpf("1e-4"):
                ratio = value / (q * q)
                if minimum_ratio_value is None or ratio < minimum_ratio_value:
                    minimum_ratio_value = ratio
                    minimum_ratio = dict(row)
                    minimum_ratio["balance_over_q_squared"] = mp.nstr(ratio, 50)
                    minimum_ratio["w=t*exp(u)"] = mp.nstr(w, 30)
    return {
        "evaluated": evaluated,
        "negative": negative,
        "minimum": minimum,
        "minimum_balance_over_q_squared_for_q_le_1e-4": minimum_ratio,
    }


def _symbolic_expansions() -> dict[str, str]:
    t, qv = sp.symbols("t q", positive=True)
    c2, c4, c6, c8, c10 = sp.symbols("c2 c4 c6 c8 c10")
    action = c2 * t**2 + c4 * t**4 + c6 * t**6 + c8 * t**8 + c10 * t**10
    q1 = sp.diff(action, t)
    q2 = sp.diff(q1, t)
    r = sp.exp(action) - 1
    m = t * q1 / (2 * r)
    elasticity = (t * (q2 - q1**2) - q1) / (2 * q1)
    balance = 6 - 2 * m - 4 * m**2 + 5 * m * elasticity
    center_series = sp.expand(sp.series(balance, t, 0, 9).removeO())

    dominant_m = qv / (sp.exp(qv) - 1)
    dominant = 6 - (2 + 5 * qv) * dominant_m - 4 * dominant_m**2
    dominant_series = sp.series(dominant, qv, 0, 8)
    return {
        "center_definition": "q(t)=c2*t^2+c4*t^4+c6*t^6+c8*t^8+c10*t^10+O(t^12)",
        "center_balance_t4_coefficient": str(sp.factor(center_series.coeff(t, 4))),
        "center_balance_t6_coefficient": str(sp.factor(center_series.coeff(t, 6))),
        "center_balance_t8_coefficient": str(sp.factor(center_series.coeff(t, 8))),
        "dominant_atom_definition": "B_dom(q)=6-(2+5q)q/(exp(q)-1)-4(q/(exp(q)-1))^2",
        "dominant_atom_series": str(dominant_series),
        "cofinal_fixed_u_limit": "B(u,t) -> 6 as t -> +infinity for fixed u",
        "large_center_scaled_limit": "u->infinity, t=w*exp(-u), q->4*pi*w^2, B->B_dom(q)",
    }


def _write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        return
    keys = sorted({key for row in rows for key in row})
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=keys)
        writer.writeheader()
        for row in rows:
            cooked = {
                key: json.dumps(value) if isinstance(value, list) else value
                for key, value in row.items()
            }
            writer.writerow(cooked)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    parser.add_argument("--actual-samples", type=int, default=24_000_000)
    parser.add_argument(
        "--mixture-samples",
        type=int,
        default=6_000_000,
        help="samples for each of the 2-, 3-, and 4-atom searches",
    )
    parser.add_argument("--chunk-size", type=int, default=20_000)
    parser.add_argument("--nmax", type=int, default=12)
    parser.add_argument("--top-k", type=int, default=100)
    parser.add_argument("--mp-dps", type=int, default=100)
    args = parser.parse_args()
    mp.mp.dps = args.mp_dps

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    started = time.time()

    actual_parts = _run_workers(
        _actual_worker,
        args.actual_samples,
        args.workers,
        (args.chunk_size, args.nmax, args.top_k),
    )
    actual = _aggregate_actual(actual_parts, args.top_k)

    actual["high_precision_top100"] = _high_precision_checks(actual["top"][:100])
    mixtures: dict[str, dict[str, Any]] = {}
    for atom_count in (2, 3, 4):
        mixture_parts = _run_workers(
            _mixture_worker,
            args.mixture_samples,
            args.workers,
            (args.chunk_size, args.top_k, atom_count),
        )
        mixture = _aggregate_mixture(mixture_parts, args.top_k)
        mixture["high_precision_top100"] = _high_precision_checks(
            mixture["top"][:100], mixture=True
        )
        for key in ("most_balanced_negative", "smallest_coefficient_spread_negative"):
            row = mixture[key]
            mixture[f"high_precision_{key}"] = (
                _high_precision_checks([row], mixture=True)[0] if row is not None else None
            )
        mixtures[f"atoms_{atom_count}"] = mixture
    symbolic = _symbolic_expansions()
    dominant = _dominant_atom_profile()
    boundary = _high_precision_boundary_layer_scan()

    result = {
        "status": "computational_reconnaissance_not_proof",
        "host": socket.gethostname(),
        "platform": platform.platform(),
        "cpu_count_logical": os.cpu_count(),
        "workers": args.workers,
        "actual_samples_requested": args.actual_samples,
        "mixture_samples_requested": args.mixture_samples,
        "nmax": args.nmax,
        "mp_dps": args.mp_dps,
        "elapsed_seconds": time.time() - started,
        "actual_source": actual,
        "finite_mixtures": mixtures,
        "dominant_atom_profile": dominant,
        "high_precision_boundary_layer": boundary,
        "symbolic": symbolic,
    }
    with (output_dir / "theta_c5_results.json").open("w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    _write_csv(output_dir / "theta_c5_actual_top.csv", actual["top"])
    mixture_rows = [row for mixture in mixtures.values() for row in mixture["top"]]
    _write_csv(output_dir / "theta_c5_finite_mixture_top.csv", mixture_rows)
    with (output_dir / "theta_c5_symbolic.txt").open("w", encoding="utf-8") as handle:
        for key, value in symbolic.items():
            handle.write(f"{key}:\n{value}\n\n")

    summary = {
        "elapsed_seconds": result["elapsed_seconds"],
        "actual_valid": actual["valid"],
        "actual_negative": actual["negative"],
        "actual_min": actual["top"][0] if actual["top"] else None,
        "mixtures": {
            key: {
                "filtered": mixture["filtered"],
                "negative": mixture["negative"],
                "minimum": mixture["top"][0] if mixture["top"] else None,
            }
            for key, mixture in mixtures.items()
        },
        "dominant_sampled_negative": dominant["sampled_negative"],
    }
    print(json.dumps(summary, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
