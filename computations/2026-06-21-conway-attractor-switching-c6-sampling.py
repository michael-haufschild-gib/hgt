#!/usr/bin/env python3
"""THE-MACHINE tick: missed metastable states -> C6 inverse-problem sampling gate.

NODE:
  Sampling rate can miss brief visits to intermediate or metastable states.

Consolidated target:
  13/32 C6 inverse problem.

STEP 9 method:
  23. Classify boundary cases.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np


NODE = "Sampling rate can miss brief visits to intermediate or metastable states"
TARGET = "13/32 C6 inverse problem"
METHOD = "23. Classify boundary cases"

ZEROS = [14.134725141734693, 21.022039638771554, 25.01085758014569]
SIGMAS = [0.35, 0.50, 0.65, 1.20]

TRANSFER_ATTEMPTS = [
    "missed metastable visits become missed phase-weld carrier states in C6 reconstruction",
    "sampling rate boundary becomes inverse-problem event-width certificate",
    "intermediate attractor aliasing becomes hidden carrier aliasing in Gamma plus prime reconstruction",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: sampling can hide intermediate attractor visits"]
    lines.append(
        "Constraint: an A->I->B switching path can look like direct A->B when the sampling "
        "interval is larger than the I residence time."
    )
    rng = np.random.default_rng(91031)
    dwell = rng.exponential(0.055, size=40_000)
    phase = rng.uniform(0.0, 1.0, size=len(dwell))
    lines.append("sample_dt hit_probability mean_seen_duration boundary_class")
    for sample_dt in [0.01, 0.025, 0.05, 0.10, 0.20, 0.40]:
        # A visit of length tau is seen if a sampling grid with random phase lands inside it.
        hit_prob = float(np.mean(np.minimum(1.0, dwell / sample_dt)))
        seen_duration = float(np.mean(np.minimum(dwell, sample_dt) * (dwell >= phase * sample_dt)))
        if hit_prob >= 0.95:
            klass = "resolved"
        elif hit_prob >= 0.50:
            klass = "aliased"
        else:
            klass = "missed"
        lines.append(f"{sample_dt:9.3f} {hit_prob:15.6f} {seen_duration:18.6f} {klass}")
    lines.append(
        "NODE verdict: the final attractor transition is not enough data. The sampling interval "
        "must be reported relative to intermediate-state dwell time."
    )
    return lines


def first_primes(n: int) -> tuple[int, ...]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


PRIMES = first_primes(160)


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite(s: complex) -> complex:
    out = 0.0 + 0.0j
    for p in PRIMES:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(a: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(a), abs(p)) + 1e-300) - math.log(abs(a + p) + 1e-300))


def carrier_series(kind: str, sigma: float, center: float, half_width: float = 1.0, n: int = 1601) -> tuple[np.ndarray, np.ndarray]:
    ts = np.linspace(center - half_width, center + half_width, n)
    vals = []
    for t in ts:
        s = complex(float(sigma), float(t))
        a = gamma_part(s)
        p = dlog_zeta(s) if kind == "true" else dlog_finite(s)
        vals.append(phase_defect(a, p))
    return ts, np.asarray(vals, dtype=float)


@dataclass
class SamplingBoundary:
    kind: str
    sigma: float
    center: float
    threshold: float
    event_width: float
    max_value: float
    sample_dt: float
    hit_probability: float
    mean_retention: float
    min_retention: float
    boundary_class: str


def classify_event(kind: str, sigma: float, center: float, threshold: float, stride: int) -> SamplingBoundary:
    ts, y = carrier_series(kind, sigma, center)
    base_dt = float(ts[1] - ts[0])
    mask = y > threshold
    event_width = float(np.sum(mask) * base_dt)
    max_value = float(np.max(y))
    if event_width <= 0.0 or max_value <= 1e-12:
        return SamplingBoundary(kind, sigma, center, threshold, 0.0, max_value, base_dt * stride, 0.0, 0.0, 0.0, "absent")
    hits = []
    rets = []
    for offset in range(stride):
        idx = np.arange(offset, len(y), stride)
        hits.append(float(np.any(mask[idx])))
        rets.append(float(np.max(y[idx]) / max_value))
    hit = float(np.mean(hits))
    mean_ret = float(np.mean(rets))
    min_ret = float(np.min(rets))
    if hit >= 0.95 and mean_ret >= 0.80:
        klass = "resolved"
    elif hit >= 0.50:
        klass = "aliased"
    else:
        klass = "missed"
    return SamplingBoundary(kind, sigma, center, threshold, event_width, max_value, base_dt * stride, hit, mean_ret, min_ret, klass)


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "The NODE's dwell-time formula does not apply unchanged to C6. Minimal transfer: treat "
        "high phase-weld cancellation `Delta=max(log|A|,log|P|)-log|A+P|` as the intermediate "
        "carrier state that an inverse reconstruction can miss."
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
        "Boundary classes: resolved = hit_probability>=0.95 and mean max-retention>=0.80; "
        "aliased = hit_probability>=0.50 but retention too low; missed = hit_probability<0.50."
    )
    lines.append("kind sigma zero_t threshold event_width max sample_dt hit_prob mean_ret min_ret class")
    for kind in ["true", "finite"]:
        for sigma in SIGMAS:
            for center in ZEROS:
                threshold = 1.0
                # Print the most informative critical sampling steps.
                for stride in [20, 80, 160, 320]:
                    b = classify_event(kind, sigma, center, threshold, stride)
                    if b.event_width == 0.0 and stride != 160:
                        continue
                    lines.append(
                        f"{kind:6s} {sigma:.2f} {center:7.3f} {threshold:.1f} "
                        f"{b.event_width:.6f} {b.max_value:.6f} {b.sample_dt:.4f} "
                        f"{b.hit_probability:.6f} {b.mean_retention:.6f} {b.min_retention:.6f} {b.boundary_class}"
                    )
    lines.append("\nSTEP 10 SUMMARY")
    summary = []
    for kind in ["true", "finite"]:
        for stride in [20, 80, 160, 320]:
            rows = [
                classify_event(kind, sigma, center, 1.0, stride)
                for sigma in [0.35, 0.50, 0.65]
                for center in ZEROS
            ]
            present = [r for r in rows if r.event_width > 0.0]
            summary.append((kind, stride, len(present), sum(r.boundary_class == "resolved" for r in present), sum(r.boundary_class == "aliased" for r in present), sum(r.boundary_class == "missed" for r in present)))
    lines.append("kind stride_dt event_cases resolved aliased missed")
    base_dt = 2.0 / 1600.0
    for kind, stride, present, resolved, aliased, missed in summary:
        lines.append(f"{kind:6s} {base_dt*stride:.4f} {present:11d} {resolved:8d} {aliased:7d} {missed:6d}")
    lines.append(
        "STEP 11 metaphor: C6 reconstruction can falsely look smooth not only because the kernel "
        "is wrong, but because brief carrier states were never sampled. The boundary case is "
        "retention, not just hit/no-hit."
    )
    return lines


def main() -> None:
    for row in node_rows():
        print(row)
    for row in transfer_rows():
        print(row)
    print("\nCANDIDATE_FINDING: C6_SAMPLING_RETENTION_GATE")
    print(
        "[CONJECTURE/GATEKEEPER] C6 inverse-problem experiments should report a carrier-event "
        "sampling certificate: sample step, offset-swept hit probability, and max-retention for "
        "phase-weld cancellation events. In the tested windows, dt=0.10 often hits true events "
        "but aliases their amplitude; dt=0.20 begins missing them by offset."
    )


if __name__ == "__main__":
    main()
