#!/usr/bin/env python3
"""Probe cross-modulus chronological carry for Euler-deletion paths.

Numerics are diagnostic only. No output from this script is used in Lean proofs.
"""

from __future__ import annotations

import argparse
import json
import math
import multiprocessing as mp
import os
from dataclasses import dataclass
from pathlib import Path

import mpmath as mpm
import numpy as np


@dataclass(frozen=True)
class Task:
    zero_index: int
    zero_imag: float
    moduli: tuple[int, ...]
    checkpoints: tuple[int, ...]
    chunk_size: int


def complex_matrix_payload(matrix: np.ndarray) -> list[list[list[float]]]:
    return [[[float(value.real), float(value.imag)] for value in row] for row in matrix]


def advance(
    endpoint: np.ndarray,
    second: np.ndarray,
    diagonal: np.ndarray,
    start: int,
    stop: int,
    moduli: tuple[int, ...],
    rho: complex,
    chunk_size: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Advance all ordered cross levels on the integer interval [start, stop]."""
    for left in range(start, stop + 1, chunk_size):
        right = min(stop, left + chunk_size - 1)
        n_int = np.arange(left, right + 1, dtype=np.int64)
        n = n_int.astype(np.float64)
        phase = np.exp(-rho * np.log(n))
        coefficients = np.stack(
            [np.where(n_int % modulus == 0, 1 - modulus, 1) for modulus in moduli]
        ).astype(np.float64)
        jumps = coefficients * phase
        before = endpoint[:, None] + np.cumsum(jumps, axis=1) - jumps
        second += before @ np.conjugate(jumps).T
        diagonal += jumps @ np.conjugate(jumps).T
        endpoint += np.sum(jumps, axis=1, dtype=np.complex128)
    return endpoint, second, diagonal


def run_task(task: Task) -> dict:
    size = len(task.moduli)
    rho = complex(0.5, task.zero_imag)
    endpoint = np.zeros(size, dtype=np.complex128)
    second = np.zeros((size, size), dtype=np.complex128)
    diagonal = np.zeros((size, size), dtype=np.complex128)
    previous = 0
    rows: list[dict] = []
    for checkpoint in task.checkpoints:
        endpoint, second, diagonal = advance(
            endpoint,
            second,
            diagonal,
            previous + 1,
            checkpoint,
            task.moduli,
            rho,
            task.chunk_size,
        )
        endpoint_product = endpoint[:, None] * np.conjugate(endpoint[None, :])
        quasi_shuffle_error = endpoint_product - second - np.conjugate(second.T) - diagonal
        carry = second - np.conjugate(second.T)
        rows.append(
            {
                "N": checkpoint,
                "endpoint_max_abs": float(np.max(np.abs(endpoint))),
                "second": complex_matrix_payload(second),
                "carry": complex_matrix_payload(carry),
                "quasi_shuffle_error_max_abs": float(np.max(np.abs(quasi_shuffle_error))),
            }
        )
        previous = checkpoint

    tail = rows[-min(6, len(rows)):]
    log_n = np.log(np.array([row["N"] for row in tail], dtype=np.float64))
    slope_real = np.zeros((size, size), dtype=np.float64)
    slope_imag = np.zeros((size, size), dtype=np.float64)
    for i in range(size):
        for j in range(size):
            values = np.array(
                [complex(*row["carry"][i][j]) for row in tail], dtype=np.complex128
            )
            slope_real[i, j] = np.polyfit(log_n, values.real, 1)[0]
            slope_imag[i, j] = np.polyfit(log_n, values.imag, 1)[0]

    return {
        "zero_index": task.zero_index,
        "rho": [0.5, task.zero_imag],
        "carry_log_slope_real": slope_real.tolist(),
        "carry_log_slope_imag": slope_imag.tolist(),
        "rows": rows,
    }


def geometric_checkpoints(max_n: int, count: int) -> tuple[int, ...]:
    raw = np.geomspace(max(100, max_n // 10_000), max_n, num=count)
    points = sorted({max(1, int(round(value))) for value in raw})
    if points[-1] != max_n:
        points.append(max_n)
    return tuple(points)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zeros", type=int, default=12)
    parser.add_argument("--max-n", type=int, default=2_000_000)
    parser.add_argument("--checkpoints", type=int, default=15)
    parser.add_argument("--workers", type=int, default=6)
    parser.add_argument("--chunk-size", type=int, default=250_000)
    parser.add_argument("--moduli", type=int, nargs="+", default=[2, 3, 5, 7])
    parser.add_argument("--out", type=Path, default=Path("cross-results.json"))
    args = parser.parse_args()

    mpm.mp.dps = 50
    zero_imag = [float(mpm.im(mpm.zetazero(index))) for index in range(1, args.zeros + 1)]
    checkpoints = geometric_checkpoints(args.max_n, args.checkpoints)
    moduli = tuple(args.moduli)
    tasks = [
        Task(index, imag, moduli, checkpoints, args.chunk_size)
        for index, imag in enumerate(zero_imag, start=1)
    ]
    workers = max(1, min(args.workers, os.cpu_count() or 1, len(tasks)))
    with mp.get_context("spawn").Pool(workers) as pool:
        results = pool.map(run_task, tasks)

    payload = {
        "purpose": "Diagnostic cross-modulus Euler-deletion carry scan; not Lean input.",
        "parameters": {
            "zeros": args.zeros,
            "max_n": args.max_n,
            "checkpoints": list(checkpoints),
            "moduli": list(moduli),
            "workers": workers,
            "chunk_size": args.chunk_size,
        },
        "results": results,
    }
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
