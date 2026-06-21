#!/usr/bin/env python3
"""THE-MACHINE tick: boundary/discretization aliasing -> affine ax+b recurrence gate.

NODE:
  Boundary conditions can interact with temporal or spatial discretization to produce aliased recurrences.

Consolidated target:
  3/32 affine ax+b.

STEP 9 method:
  20. Name the missing lemma.
"""

from __future__ import annotations

import itertools
import math

import numpy as np


NODE = "Boundary conditions can interact with temporal or spatial discretization to produce aliased recurrences"
TARGET = "3/32 affine ax+b"
METHOD = "20. Name the missing lemma"

TRANSFER_ATTEMPTS = [
    "boundary discretization aliasing becomes affine log-grid recurrence aliasing",
    "stochastic boundary recurrences become ax+b frequency passport failures",
    "boundary-condition artifacts become universal-curvature affine orbit artifacts",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def autocorr_at_lag(x: np.ndarray, lag: int) -> float:
    return float(abs(np.vdot(x[:-lag], x[lag:]) / (np.vdot(x[:-lag], x[:-lag]) + 1e-300)))


def real_recurrence_at_lag(x: np.ndarray, lag: int) -> float:
    return float(np.real(np.vdot(x[:-lag], x[lag:]) / (np.vdot(x[:-lag], x[:-lag]) + 1e-300)))


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: boundary plus discretization creates recurrence artifacts"]
    lines.append(
        "Constraint: a stochastic path on a periodic boundary can show recurrence at the grid "
        "period even when the unconstrained increments have no such period."
    )
    rng = np.random.default_rng(44019)
    n = 4096
    lag = 37
    noise = rng.normal(0.0, 0.015, size=n)
    periodic_increments = 1.0 / lag + noise
    irrational_increments = math.sqrt(2.0) / lag + noise
    circle = np.cumsum(periodic_increments) % 1.0
    irrational_circle = np.cumsum(irrational_increments) % 1.0
    centered_circle = np.exp(2j * math.pi * circle)
    centered_irrational = np.exp(2j * math.pi * irrational_circle)
    lines.append("case recurrence_lag autocorr note")
    lines.append(f"periodic_boundary {lag:14d} {real_recurrence_at_lag(centered_circle, lag):.6f} wrapped rational drift")
    lines.append(f"irrational_drift   {lag:14d} {real_recurrence_at_lag(centered_irrational, lag):.6f} same boundary, irrational drift")
    lines.append(
        "NODE verdict: recurrence is not intrinsic to the stochastic increments; it is created by "
        "the periodic boundary interacting with the discretized drift."
    )
    return lines


def affine_modes(k: int = 3, bound: int = 3) -> np.ndarray:
    return np.asarray([m for m in itertools.product(range(-bound, bound + 1), repeat=k) if any(m)], dtype=float)


def affine_signal(omega: np.ndarray, coeff: np.ndarray, dt: float, n: int) -> np.ndarray:
    steps = np.arange(n, dtype=float)
    x = np.zeros(n, dtype=complex)
    for w, c in zip(omega, coeff):
        x += c * np.exp(-1j * w * dt * steps)
    return x


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "The NODE recurrence formula does not apply unchanged. Minimal affine transfer: use "
        "boundary modes e_m with frequencies omega_m=m.log(p); discretizing log(p) onto a "
        "periodic frequency grid imposes artificial recurrences on the affine orbit."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER ATTEMPTS")
    best: tuple[int, int, str] | None = None
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        dist = levenshtein(NODE.lower(), attempt.lower())
        lines.append(f"{i}. distance={dist:3d} {attempt}")
        if best is None or dist < best[0]:
            best = (dist, i, attempt)
    assert best is not None
    lines.append(f"selected={best[1]} {best[2]}")
    lines.append(f"\nSTEP 9 METHOD {METHOD}")
    lines.append(
        "Missing lemma: affine recurrence passport. Any recurrence observed in a finite ax+b "
        "mode experiment must survive de-periodizing the log grid and changing the boundary "
        "period; otherwise it is universal affine-orbit aliasing, not seam holonomy."
    )
    primes = np.asarray([2.0, 3.0, 5.0])
    logs = np.log(primes)
    modes = affine_modes(k=3, bound=3)
    rng = np.random.default_rng(51277)
    coeff = rng.normal(size=len(modes)) + 1j * rng.normal(size=len(modes))
    coeff = coeff / np.linalg.norm(coeff)
    n = 4096
    recurrence_lag = 128
    lines.append(
        "h max_log_error exact_recur quantized_recur jittered_quant_recur curvature_error_bound recurrence_lag"
    )
    for h in [1 / 4, 1 / 8, 1 / 16, 1 / 32, 1 / 64, 1 / 128]:
        qlogs = np.round(logs / h) * h
        exact_omega = modes @ logs
        quant_omega = modes @ qlogs
        dt = 2.0 * math.pi / (h * recurrence_lag)
        exact = autocorr_at_lag(affine_signal(exact_omega, coeff, dt, n), recurrence_lag)
        quant = autocorr_at_lag(affine_signal(quant_omega, coeff, dt, n), recurrence_lag)
        jitter = autocorr_at_lag(affine_signal(quant_omega, coeff, dt * 1.007, n), recurrence_lag)
        err = float(np.max(np.abs(qlogs - logs)))
        # Universal curvature is -log p; quantization perturbs it by at most this error.
        lines.append(
            f"{h:.7f} {err:.9f} {exact:.6f} {quant:.6f} {jitter:.6f} {err:.9f} {recurrence_lag}"
        )
    lines.append(
        "STEP 10 verdict: arbitrarily fine log-grid approximations can retain a perfect imposed "
        "recurrence at the boundary period while exact prime logs do not. The recurrence is "
        "therefore affine-grid aliasing unless the passport lemma is satisfied."
    )
    lines.append(
        "STEP 11 metaphor: the affine curvature [partial_s,M_p]=-log p can be approximated well "
        "while the finite boundary condition manufactures recurrence. Curvature-level evidence "
        "remains RH-blind; recurrence must be tested in the holonomy/seam register."
    )
    return lines


def main() -> None:
    for row in node_rows():
        print(row)
    for row in transfer_rows():
        print(row)
    print("\nCANDIDATE_FINDING: AFFINE_RECURRENCE_PASSPORT_GATE")
    print(
        "[CONJECTURE/GATEKEEPER] Finite ax+b experiments need an affine recurrence passport: "
        "reported recurrences must survive log-grid deperiodization and boundary-period changes. "
        "Otherwise perfect recurrence can be manufactured inside the universal curvature layer."
    )


if __name__ == "__main__":
    main()
