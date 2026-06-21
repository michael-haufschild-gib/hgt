#!/usr/bin/env python3
"""THE-MACHINE tick: SOC timescale separation -> C4 cross-lane correlation.

NODE:
  The separation of timescales between loading and avalanching is a core
  assumption, not a cosmetic detail.

Consolidated target:
  C4 -- cross-lane correlation length xi_sigma.

STEP 9 method:
  17. Change representation.
"""

from __future__ import annotations

import math
from collections import deque

import mpmath as mp
import numpy as np


NODE = (
    "the separation of timescales between loading and avalanching is a core "
    "assumption not a cosmetic detail"
)

TRANSFER_ATTEMPTS = [
    "C4 cross lane event sheets need separation between slow loading and fast phase avalanches",
    "sigma lane correlation length changes when phase defects are temporally coarsened",
    "without timescale separation C4 avalanche components become artificial merged sheets",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def merge_intervals(starts: np.ndarray, durations: np.ndarray) -> list[tuple[float, float, int]]:
    intervals = sorted((float(s), float(s + d), 1) for s, d in zip(starts, durations))
    merged: list[tuple[float, float, int]] = []
    for a, b, n in intervals:
        if not merged or a > merged[-1][1]:
            merged.append((a, b, n))
        else:
            pa, pb, pn = merged[-1]
            merged[-1] = (pa, max(pb, b), pn + n)
    return merged


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606212359)
    lines = ["STEP 6 NODE TEST: SOC loading/avalanche timescale separation"]
    lines.append(
        "Synthetic avalanches have Pareto durations. If new loading events "
        "arrive before avalanches end, observed intervals merge and the "
        "avalanche distribution is no longer the microscopic one."
    )
    lines.append("drive_mean duration_mean overlap_fraction true_events observed_events mean_merge max_merge observed_mean_duration")
    duration = (rng.pareto(1.6, size=1200) + 1.0)
    for drive_mean in [0.25, 0.5, 1.0, 2.0, 5.0, 10.0]:
        waits = rng.exponential(drive_mean, size=len(duration))
        starts = np.cumsum(waits)
        merged = merge_intervals(starts, duration)
        counts = np.array([m[2] for m in merged], dtype=float)
        overlap = float(np.mean(counts > 1))
        obs_dur = np.array([b - a for a, b, _ in merged], dtype=float)
        lines.append(
            f"{drive_mean:5.2f} {float(np.mean(duration)):.3f} {overlap:.4f} "
            f"{len(duration):4d} {len(merged):4d} {float(np.mean(counts)):.3f} "
            f"{int(np.max(counts))} {float(np.mean(obs_dur)):.3f}"
        )
    lines.append(
        "NODE verdict: when drive_mean is comparable to avalanche duration, "
        "the observed avalanche units are merged composites. Timescale "
        "separation is a definitional constraint."
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


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def build_fields(sigmas: list[float], window: tuple[float, float], samples: int, primes: tuple[int, ...], rng) -> dict[str, np.ndarray]:
    fields = {k: np.zeros((samples, len(sigmas)), dtype=float) for k in ["true", "finite", "random"]}
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            fp = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            fields["true"][j, i] = phase_defect(g, zp)
            fields["finite"][j, i] = phase_defect(g, fp)
            fields["random"][j, i] = phase_defect(g, rp)
    return fields


def temporal_close(events: np.ndarray, gap: int) -> np.ndarray:
    if gap <= 0:
        return events.copy()
    out = events.copy()
    n, lanes = out.shape
    for lane in range(lanes):
        idx = np.flatnonzero(events[:, lane])
        for a, b in zip(idx, idx[1:]):
            if b - a - 1 <= gap:
                out[a : b + 1, lane] = True
    return out


def component_metrics(events: np.ndarray) -> dict[str, float]:
    n_t, n_s = events.shape
    seen = np.zeros_like(events, dtype=bool)
    comps = []
    for t in range(n_t):
        for s in range(n_s):
            if not events[t, s] or seen[t, s]:
                continue
            q = deque([(t, s)])
            seen[t, s] = True
            cells = []
            while q:
                a, b = q.popleft()
                cells.append((a, b))
                for da, db in [(1, 0), (-1, 0), (0, 1), (0, -1)]:
                    aa, bb = a + da, b + db
                    if 0 <= aa < n_t and 0 <= bb < n_s and events[aa, bb] and not seen[aa, bb]:
                        seen[aa, bb] = True
                        q.append((aa, bb))
            comps.append(cells)
    if not comps:
        return {"count": 0.0, "max_area": 0.0, "max_sigma_span": 0.0, "mean_area": 0.0}
    areas = np.array([len(c) for c in comps], dtype=float)
    spans = np.array([max(x[1] for x in c) - min(x[1] for x in c) + 1 for c in comps], dtype=float)
    return {
        "count": float(len(comps)),
        "max_area": float(np.max(areas)),
        "max_sigma_span": float(np.max(spans)),
        "mean_area": float(np.mean(areas)),
    }


def transfer_rows() -> list[str]:
    rng = np.random.default_rng(2606212417)
    primes = first_primes(160)
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "SOC timescale-separation formulas do not apply unchanged. The C4 "
        "transfer uses phase-weld event sheets and changes representation "
        "from lane correlations to connected sigma-time avalanche components."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 17: CHANGE REPRESENTATION")
    lines.append(
        "C4 field -> avalanche components in the sigma-time event grid. "
        "Temporal gap-closing emulates insufficient separation between loading "
        "and avalanche relaxation."
    )
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    fields = build_fields(sigmas, (100.0, 170.0), 560, primes, rng)
    threshold = float(np.quantile(fields["true"], 0.78))
    lines.append(f"threshold=true_q78={threshold:.6f}")
    lines.append("kind gap event_fraction comp_count max_area max_sigma_span mean_area")
    for kind in ["true", "finite", "random"]:
        base = fields[kind] > threshold
        for gap in [0, 1, 2, 4, 8, 16]:
            ev = temporal_close(base, gap)
            m = component_metrics(ev)
            lines.append(
                f"{kind:6s} {gap:2d} {float(np.mean(ev)):.4f} {m['count']:7.0f} "
                f"{m['max_area']:8.0f} {m['max_sigma_span']:6.0f} {m['mean_area']:.3f}"
            )
    lines.append(
        "\nProvisional verdict: if true C4 survives at gap 0 and controls only "
        "become sheet-like after large gap-closing, C4 needs an event-resolution "
        "gate rather than raw coarsened component sizes."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: SOC timescale separation -> C4")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 12/32 C4 cross-lane correlation")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
