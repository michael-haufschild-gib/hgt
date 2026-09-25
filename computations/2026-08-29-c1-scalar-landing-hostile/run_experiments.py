#!/usr/bin/env python3
"""Hostile numerical audit of C1's exact scalar first-trace landing.

Diagnostic only. No output from this script is admissible in a Lean proof.

The formulas are literal transcriptions of:
  GammaSewnMobiusApertureStokesGlobalMeanFirstTrace.lean
  GammaSewnMobiusApertureStokesCofinalPluckerSpectralOperator.lean
  GammaSewnMobiusApertureStokesCriticalAdjacentPrimeCofinalFeshbach.lean
  GammaSewnMobiusApertureStokesOrderedPrimeDepthPluckerChirality.lean
  GammaSewnMobiusApertureStokesSquaredCompactMarkovCandidate.lean
  GammaSewnMobiusApertureStokesInverseTilt.lean
  PrimeArchThetaCumulantMinor.lean

It computes, on nested finite rectangles of packet indices,

  C1 trace = raw first moment - sum_u node(u) occupation(u)^2

and compares it with thetaCuspNormalizedEvenMoment 1 / 2.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import multiprocessing as mp_pool
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import mpmath as mp
import numpy as np


PAIR_LEFT = np.array([0, 0, 0, 1, 1, 2], dtype=np.int64)
PAIR_RIGHT = np.array([1, 2, 3, 2, 3, 3], dtype=np.int64)


def primes_first(count: int) -> np.ndarray:
    """Return first count primes via an Eratosthenes sieve."""
    if count < 1:
        return np.empty(0, dtype=np.int64)
    if count < 6:
        limit = 15
    else:
        n = float(count)
        limit = int(n * (math.log(n) + math.log(math.log(n))) + 32)
    while True:
        sieve = np.ones(limit + 1, dtype=np.bool_)
        sieve[:2] = False
        for p in range(2, math.isqrt(limit) + 1):
            if sieve[p]:
                sieve[p * p :: p] = False
        values = np.flatnonzero(sieve)
        if values.size >= count:
            return values[:count].astype(np.int64)
        limit *= 2


def hostile_aperture() -> float:
    l2 = math.log(2.0)
    l3 = math.log(3.0)
    rates = np.array([0.5 * l2, 1.5 * l2, 0.5 * l3, 1.5 * l3])
    return float(1.0 / (1.0 + np.sum(1.0 / rates)))


def inverse_tilt_half(p: np.ndarray) -> np.ndarray:
    """Literal gammaSewnMobiusApertureStokesInverseTilt (1/2) p."""
    p = np.asarray(p, dtype=np.float64)
    logp = np.log(p)
    q = np.exp(-0.5 * logp)
    transverse = np.exp(-logp)
    semilocal = np.cosh(logp) ** (-0.5)
    recovery = (1.0 + q) / np.sqrt(q)
    contraction = 0.5 * np.sqrt(semilocal) * recovery
    return logp * q / (contraction * (transverse / (1.0 + transverse)) * (1.0 - q))


def physical_nodes(primes: np.ndarray, depths: np.ndarray) -> np.ndarray:
    """Squared reciprocal Stokes-gap node at s=1/2."""
    inv_tilt = inverse_tilt_half(primes)[None, :]
    gap = (depths[:, None] + 1.0) * inv_tilt
    return 1.0 / (gap * gap)


def packet_arrays(primes: np.ndarray, max_depth: int, aperture: float):
    """Return denominator terms, four marginal means, and four nodes.

    primes has length packet_count + 1 and supplies adjacent packet edges.
    Array shape is (max_depth + 1, packet_count).
    """
    p = primes[:-1].astype(np.float64)
    q = primes[1:].astype(np.float64)
    lp = np.log(p)[None, :]
    lq = np.log(q)[None, :]
    e = np.arange(max_depth + 1, dtype=np.float64)[:, None]
    rates = np.stack(
        [
            np.broadcast_to((e + 0.5) * lp, (max_depth + 1, p.size)),
            np.broadcast_to((e + 1.5) * lp, (max_depth + 1, p.size)),
            np.broadcast_to((e + 0.5) * lq, (max_depth + 1, p.size)),
            np.broadcast_to((e + 1.5) * lq, (max_depth + 1, p.size)),
        ],
        axis=0,
    )
    amp = np.stack(
        [
            np.broadcast_to(lp / (p[None, :] + 1.0), rates.shape[1:]),
            np.broadcast_to(lp / (p[None, :] + 1.0), rates.shape[1:]),
            np.broadcast_to(lq / (q[None, :] + 1.0), rates.shape[1:]),
            np.broadcast_to(lq / (q[None, :] + 1.0), rates.shape[1:]),
        ],
        axis=0,
    )
    weights = []
    for left, right in zip(PAIR_LEFT, PAIR_RIGHT):
        lam = rates[left]
        mu = rates[right]
        plucker = (
            2.0
            * aperture
            * (lam - mu)
            / ((lam * lam - aperture * aperture) * (mu * mu - aperture * aperture))
        )
        weights.append(plucker * plucker * (amp[left] * amp[right]) ** 2)
    raw = np.stack(weights, axis=0)
    partition = np.sum(raw, axis=0)
    prob = raw / partition[None, :, :]
    means = np.stack(
        [
            prob[0] + prob[1] + prob[2],
            prob[0] + prob[3] + prob[4],
            prob[1] + prob[3] + prob[5],
            prob[2] + prob[4] + prob[5],
        ],
        axis=0,
    )
    total_fisher = (2.0 / 3.0) * (2.0 * lp * lp + 2.0 * lq * lq)
    denominator = partition * total_fisher

    node_p = physical_nodes(p, np.arange(max_depth + 2, dtype=np.float64))
    node_q = physical_nodes(q, np.arange(max_depth + 2, dtype=np.float64))
    nodes = np.stack(
        [node_p[:-1], node_p[1:], node_q[:-1], node_q[1:]], axis=0
    )
    return denominator, means, nodes


@dataclass(frozen=True)
class Rectangle:
    packets: int
    max_depth: int


_WORKER_PRIMES: np.ndarray | None = None
_WORKER_APERTURE: float | None = None
_WORKER_RECT: Rectangle | None = None
_WORKER_Z: float | None = None


def init_worker(primes, aperture, rectangle, normalizer):
    global _WORKER_PRIMES, _WORKER_APERTURE, _WORKER_RECT, _WORKER_Z
    _WORKER_PRIMES = primes
    _WORKER_APERTURE = aperture
    _WORKER_RECT = rectangle
    _WORKER_Z = normalizer


def packet_chunk(bounds: tuple[int, int]):
    start, stop = bounds
    assert _WORKER_PRIMES is not None
    assert _WORKER_APERTURE is not None
    assert _WORKER_RECT is not None
    subprimes = _WORKER_PRIMES[start : stop + 1]
    denominator, means, nodes = packet_arrays(
        subprimes, _WORKER_RECT.max_depth, _WORKER_APERTURE
    )
    raw = np.sum(denominator * np.sum(nodes * means, axis=0), dtype=np.float64)
    return float(np.sum(denominator, dtype=np.float64)), float(raw)


def occupation_chunk(bounds: tuple[int, int]):
    """Collision energy on physical prime columns [start, stop)."""
    start, stop = bounds
    assert _WORKER_PRIMES is not None
    assert _WORKER_APERTURE is not None
    assert _WORKER_RECT is not None
    assert _WORKER_Z is not None
    packet_lo = max(0, start - 1)
    packet_hi = min(_WORKER_RECT.packets, stop)
    subprimes = _WORKER_PRIMES[packet_lo : packet_hi + 1]
    denominator, means, _ = packet_arrays(
        subprimes, _WORKER_RECT.max_depth, _WORKER_APERTURE
    )
    weighted = denominator[None, :, :] * means / _WORKER_Z
    out = 0.0
    depth_count = _WORKER_RECT.max_depth + 1
    for physical_n in range(start, stop):
        occ = np.zeros(depth_count + 1, dtype=np.float64)
        if physical_n < _WORKER_RECT.packets:
            j = physical_n - packet_lo
            occ[:depth_count] += weighted[0, :, j]
            occ[1:] += weighted[1, :, j]
        if physical_n > 0 and physical_n - 1 < _WORKER_RECT.packets:
            j = physical_n - 1 - packet_lo
            occ[:depth_count] += weighted[2, :, j]
            occ[1:] += weighted[3, :, j]
        node = physical_nodes(
            _WORKER_PRIMES[physical_n : physical_n + 1].astype(np.float64),
            np.arange(depth_count + 1, dtype=np.float64),
        )[:, 0]
        out += float(np.sum(node * occ * occ, dtype=np.float64))
    return out


def chunks(total: int, width: int) -> list[tuple[int, int]]:
    return [(start, min(total, start + width)) for start in range(0, total, width)]


def compute_rectangle(rect: Rectangle, primes: np.ndarray, aperture: float, workers: int):
    packet_bounds = chunks(rect.packets, 128)
    ctx = mp_pool.get_context("fork")
    with ctx.Pool(
        workers,
        initializer=init_worker,
        initargs=(primes, aperture, rect, 1.0),
    ) as pool:
        packet_parts = pool.map(packet_chunk, packet_bounds)
    normalizer = math.fsum(x[0] for x in packet_parts)
    raw_unnormalized = math.fsum(x[1] for x in packet_parts)
    physical_bounds = chunks(rect.packets + 1, 128)
    with ctx.Pool(
        workers,
        initializer=init_worker,
        initargs=(primes, aperture, rect, normalizer),
    ) as pool:
        collision_parts = pool.map(occupation_chunk, physical_bounds)
    collision = math.fsum(collision_parts)
    raw = raw_unnormalized / normalizer
    return {
        "packets": rect.packets,
        "max_depth": rect.max_depth,
        "normalizer": normalizer,
        "raw_first_moment": raw,
        "collision_energy": collision,
        "c1_trace": raw - collision,
    }


def theta_phi(x: mp.mpf) -> mp.mpf:
    """Literal thetaCuspFullSource, stabilized by exact evenness."""
    x = abs(mp.mpf(x))
    ex = mp.exp(x)
    total = mp.mpf("0")
    n = 1
    threshold = mp.mpf(10) ** (-(mp.mp.dps + 10))
    largest = mp.mpf("0")
    while True:
        t = mp.mpf(n) * ex
        term = mp.exp(x / 2) * 2 * mp.pi * (
            2 * mp.pi * t**4 - 3 * t**2
        ) * mp.exp(-mp.pi * t**2)
        total += term
        largest = max(largest, abs(term))
        if n > 3 and abs(term) < threshold * max(largest, threshold):
            break
        n += 1
    return total


def xi_completed(s: mp.mpf) -> mp.mpf:
    return (
        mp.mpf("0.5")
        * s
        * (s - 1)
        * mp.pi ** (-s / 2)
        * mp.gamma(s / 2)
        * mp.zeta(s)
    )


def theta_target(dps: int) -> dict[str, str]:
    """Use the corpus derivative bridge instead of slow quadrature.

    Xi(t)=xi(1/2+i*t), so the Lean identity
      Xi''(0) = -thetaCuspRawEvenMoment 1
    gives raw moment one = xi''(1/2). Raw moment zero is xi(1/2).
    A lower-precision direct source quadrature is performed separately by the verifier.
    """
    mp.mp.dps = dps
    center = mp.mpf("0.5")
    m0 = xi_completed(center)
    m1 = mp.diff(xi_completed, center, 2)
    normalized = m1 / m0
    return {
        "raw_moment_zero": mp.nstr(m0, dps - 5),
        "raw_moment_one": mp.nstr(m1, dps - 5),
        "normalized_moment_one": mp.nstr(normalized, dps - 5),
        "target_half": mp.nstr(normalized / 2, dps - 5),
    }


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def parse_rectangles(values: Iterable[str]) -> list[Rectangle]:
    out = []
    for value in values:
        packets, depth = value.split(":", maxsplit=1)
        out.append(Rectangle(int(packets), int(depth)))
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=min(128, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=70)
    parser.add_argument(
        "--rectangle",
        action="append",
        default=[],
        help="nested packet_count:max_depth; may be repeated",
    )
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    args = parser.parse_args()
    rectangles = parse_rectangles(args.rectangle) if args.rectangle else [
        Rectangle(1000, 64),
        Rectangle(5000, 128),
        Rectangle(20000, 256),
        Rectangle(100000, 512),
    ]
    max_packets = max(rect.packets for rect in rectangles)
    primes = primes_first(max_packets + 1)
    aperture = hostile_aperture()
    theta = theta_target(args.dps)
    target = float(mp.mpf(theta["target_half"]))
    results = []
    for rect in rectangles:
        record = compute_rectangle(rect, primes[: rect.packets + 1], aperture, args.workers)
        record["target_half"] = target
        record["trace_minus_target"] = record["c1_trace"] - target
        record["relative_trace_target_error"] = (record["c1_trace"] - target) / target
        results.append(record)
        print(json.dumps(record, sort_keys=True), flush=True)
    payload = {
        "scope": "diagnostic only; forbidden in Lean proofs",
        "workers": args.workers,
        "aperture": aperture,
        "theta": theta,
        "rectangles": results,
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"wrote {args.output} sha256={sha256(args.output)}", flush=True)


if __name__ == "__main__":
    main()
