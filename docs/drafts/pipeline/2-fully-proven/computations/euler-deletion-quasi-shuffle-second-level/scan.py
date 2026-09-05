#!/usr/bin/env python3
"""Numerically probe chronological level-two behavior of Euler-deletion paths.

Numerics are diagnostic only.  No result from this script is used in Lean proofs.
"""

from __future__ import annotations

import argparse
import json
import math
import multiprocessing as mp
import os
from dataclasses import asdict, dataclass
from pathlib import Path

import mpmath as mpm
import numpy as np


@dataclass(frozen=True)
class Task:
    zero_index: int
    zero_imag: float
    modulus: int
    checkpoints: tuple[int, ...]


def advance(state: tuple[complex, complex, float], start: int, stop: int,
            modulus: int, rho: complex) -> tuple[complex, complex, float]:
    """Advance endpoint, chronological second level, and diagonal energy on [start, stop]."""
    endpoint, second, energy = state
    n = np.arange(start, stop + 1, dtype=np.float64)
    coeff = np.where((n.astype(np.int64) % modulus) == 0, 1 - modulus, 1).astype(np.float64)
    jump = coeff * np.exp(-rho * np.log(n))
    before = endpoint + np.cumsum(jump) - jump
    second += np.sum(before * np.conjugate(jump), dtype=np.complex128)
    endpoint += np.sum(jump, dtype=np.complex128)
    energy += float(np.vdot(jump, jump).real)
    return endpoint, second, energy


def run_task(task: Task) -> dict:
    rho = complex(0.5, task.zero_imag)
    state: tuple[complex, complex, float] = (0j, 0j, 0.0)
    previous = 0
    rows: list[dict] = []
    for checkpoint in task.checkpoints:
        state = advance(state, previous + 1, checkpoint, task.modulus, rho)
        endpoint, second, energy = state
        rows.append(
            {
                "N": checkpoint,
                "endpoint_abs": abs(endpoint),
                "energy": energy,
                "second_re": second.real,
                "second_im": second.imag,
                "renormalized_second_re": second.real + 0.5 * energy,
                "quasi_shuffle_error": abs(abs(endpoint) ** 2 - (energy + 2 * second.real)),
            }
        )
        previous = checkpoint

    tail = rows[-min(6, len(rows)):]
    log_n = np.log(np.array([row["N"] for row in tail], dtype=np.float64))
    imag = np.array([row["second_im"] for row in tail], dtype=np.float64)
    energy = np.array([row["energy"] for row in tail], dtype=np.float64)
    imag_log_slope = float(np.polyfit(log_n, imag, 1)[0]) if len(tail) >= 2 else math.nan
    energy_log_slope = float(np.polyfit(log_n, energy, 1)[0]) if len(tail) >= 2 else math.nan
    return {
        "zero_index": task.zero_index,
        "rho": [0.5, task.zero_imag],
        "modulus": task.modulus,
        "imag_log_slope_tail": imag_log_slope,
        "energy_log_slope_tail": energy_log_slope,
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
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--moduli", type=int, nargs="+", default=[2, 3, 5, 7])
    parser.add_argument("--out", type=Path, default=Path("results.json"))
    args = parser.parse_args()

    mpm.mp.dps = 50
    zero_imag = [float(mpm.im(mpm.zetazero(index))) for index in range(1, args.zeros + 1)]
    checkpoints = geometric_checkpoints(args.max_n, args.checkpoints)
    tasks = [
        Task(index, imag, modulus, checkpoints)
        for index, imag in enumerate(zero_imag, start=1)
        for modulus in args.moduli
    ]
    workers = max(1, min(args.workers, os.cpu_count() or 1, len(tasks)))
    with mp.get_context("spawn").Pool(workers) as pool:
        results = pool.map(run_task, tasks)

    payload = {
        "purpose": "Diagnostic scan of Euler-deletion chronological second levels; not Lean input.",
        "parameters": {
            "zeros": args.zeros,
            "max_n": args.max_n,
            "checkpoints": list(checkpoints),
            "moduli": args.moduli,
            "workers": workers,
        },
        "results": results,
    }
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
