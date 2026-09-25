#!/usr/bin/env python3
"""Independent structural verifier for the C1 diagnostic computation."""

from __future__ import annotations

import importlib.util
import json
import math
import sys
from pathlib import Path

import mpmath as mp
import numpy as np


ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("experiment", ROOT / "run_experiments.py")
experiment = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = experiment
spec.loader.exec_module(experiment)


def direct_theta_quadrature() -> float:
    """Independent fixed Gauss-Legendre quadrature of literal positive source."""
    nodes, weights = np.polynomial.legendre.leggauss(1024)
    x = 2.5 * (nodes + 1.0)
    w = 2.5 * weights
    ex = np.exp(x)
    phi = np.zeros_like(x)
    for n in range(1, 24):
        t = n * ex
        phi += (
            np.exp(x / 2.0)
            * 2.0
            * np.pi
            * (2.0 * np.pi * t**4 - 3.0 * t**2)
            * np.exp(-np.pi * t**2)
        )
    m0 = 2.0 * float(np.sum(w * phi))
    m1 = 2.0 * float(np.sum(w * x * x * phi))
    return m1 / m0 / 2.0


def mp_packet(p: int, q: int, depth: int, aperture: mp.mpf):
    lp, lq = mp.log(p), mp.log(q)
    rates = [
        (depth + mp.mpf("0.5")) * lp,
        (depth + mp.mpf("1.5")) * lp,
        (depth + mp.mpf("0.5")) * lq,
        (depth + mp.mpf("1.5")) * lq,
    ]
    amps = [lp / (p + 1), lp / (p + 1), lq / (q + 1), lq / (q + 1)]
    pairs = list(zip(experiment.PAIR_LEFT.tolist(), experiment.PAIR_RIGHT.tolist()))
    raw = []
    for left, right in pairs:
        lam, mu = rates[left], rates[right]
        plucker = 2 * aperture * (lam - mu) / (
            (lam**2 - aperture**2) * (mu**2 - aperture**2)
        )
        raw.append(plucker**2 * (amps[left] * amps[right]) ** 2)
    part = mp.fsum(raw)
    prob = [value / part for value in raw]
    means = [
        prob[0] + prob[1] + prob[2],
        prob[0] + prob[3] + prob[4],
        prob[1] + prob[3] + prob[5],
        prob[2] + prob[4] + prob[5],
    ]
    total = mp.mpf(2) / 3 * (2 * lp**2 + 2 * lq**2)
    return part * total, means


def verify_packet_transcription() -> None:
    mp.mp.dps = 70
    primes = experiment.primes_first(7)
    aperture_float = experiment.hostile_aperture()
    aperture = 1 / (
        1
        + 1 / (mp.log(2) / 2)
        + 1 / (3 * mp.log(2) / 2)
        + 1 / (mp.log(3) / 2)
        + 1 / (3 * mp.log(3) / 2)
    )
    denominator, means, _ = experiment.packet_arrays(primes, 4, aperture_float)
    assert np.max(np.abs(np.sum(means, axis=0) - 2.0)) < 2e-15
    assert np.min(denominator) > 0.0
    for n in range(6):
        for depth in range(5):
            direct_den, direct_means = mp_packet(
                int(primes[n]), int(primes[n + 1]), depth, aperture
            )
            assert math.isclose(float(direct_den), denominator[depth, n], rel_tol=3e-14)
            for i in range(4):
                assert math.isclose(float(direct_means[i]), means[i, depth, n], rel_tol=3e-14)


def main() -> None:
    payload = json.loads((ROOT / "results.json").read_text())
    rows = payload["rectangles"]
    assert len(rows) == 4
    assert [row["packets"] for row in rows] == [1000, 5000, 20000, 100000]
    assert [row["max_depth"] for row in rows] == [64, 128, 256, 512]
    target = float(mp.mpf(payload["theta"]["target_half"]))
    quadrature_target = direct_theta_quadrature()
    assert abs(target - quadrature_target) < 2e-12
    verify_packet_transcription()
    for row in rows:
        assert row["normalizer"] > 0.0
        assert row["raw_first_moment"] > row["collision_energy"] > 0.0
        assert math.isclose(
            row["c1_trace"],
            row["raw_first_moment"] - row["collision_energy"],
            rel_tol=0.0,
            abs_tol=2e-17,
        )
        assert row["trace_minus_target"] < -0.007
    for before, after in zip(rows, rows[1:]):
        assert abs(after["c1_trace"] - before["c1_trace"]) < 1e-10
    assert abs(rows[-1]["c1_trace"] - rows[-2]["c1_trace"]) < 1e-15
    print(
        "verified: direct theta quadrature, independent packet formulas, "
        "nested convergence, and stable C1 landing mismatch"
    )


if __name__ == "__main__":
    main()
