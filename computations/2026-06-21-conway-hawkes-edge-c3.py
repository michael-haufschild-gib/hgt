#!/usr/bin/env python3
"""THE-MACHINE tick: Hawkes edge correction -> C3 phase Sobolev.

NODE:
  Edge correction matters because events before the observation window can
  still excite observed events.

Consolidated target:
  11/32 C3 -- H1/Sobolev phase regularity gap.

STEP 9 method:
  20. Name the missing lemma.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


NODE = "Edge correction matters because events before the observation window can still excite observed events"
TARGET = "11/32 C3 H1/Sobolev"
METHOD = "20. Name the missing lemma"

TRANSFER_ATTEMPTS = [
    "pre-window excitation becomes guard-band phase energy in the C3 Sobolev statistic",
    "C3 phase regularity needs edge correction before measuring long-run coherence",
    "events before the window become phase history before the t-interval",
]


C4 = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
gamma_part = C4["gamma_part"]
dlog_zeta = C4["dlog_zeta"]
dlog_finite = C4["dlog_finite"]
first_primes = C4["first_primes"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def simulate_hawkes(mu: float, alpha: float, beta: float, start: float, stop: float, rng) -> list[float]:
    """Ogata thinning for exponential Hawkes with kernel alpha exp(-beta t)."""

    t = start
    excitation = 0.0
    events: list[float] = []
    while t < stop:
        lam_bar = mu + excitation
        if lam_bar <= 0.0:
            break
        t_next = t + float(rng.exponential(1.0 / lam_bar))
        excitation *= math.exp(-beta * (t_next - t))
        t = t_next
        if t >= stop:
            break
        lam = mu + excitation
        if rng.uniform() <= lam / lam_bar:
            events.append(t)
            excitation += alpha
    return events


def hawkes_intensity_at(times: np.ndarray, events: list[float], mu: float, alpha: float, beta: float) -> np.ndarray:
    out = np.full_like(times, mu, dtype=float)
    ev = np.asarray(events, dtype=float)
    for i, t in enumerate(times):
        past = ev[ev < t]
        if len(past):
            out[i] += float(np.sum(alpha * np.exp(-beta * (t - past))))
    return out


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606215539)
    mu, beta, branching = 0.25, 1.15, 0.72
    alpha = branching * beta
    events = simulate_hawkes(mu, alpha, beta, -80.0, 80.0, rng)
    pre = [t for t in events if t < 0.0]
    obs = [t for t in events if 0.0 <= t <= 60.0]
    grid = np.linspace(0.0, 60.0, 600)
    lam_full = hawkes_intensity_at(grid, events, mu, alpha, beta)
    lam_trunc = hawkes_intensity_at(grid, obs, mu, alpha, beta)
    missing = lam_full - lam_trunc
    segs = [(0.0, 5.0), (5.0, 15.0), (15.0, 60.0)]
    lines = ["STEP 5/6 NODE TEST: Hawkes window-edge correction"]
    lines.append(
        "Constraint: the conditional intensity on [0,T] is not determined by observed-window "
        "events alone; pre-window events leave an excitation tail."
    )
    lines.append(
        f"params mu={mu:.3f} alpha={alpha:.3f} beta={beta:.3f} branching={alpha/beta:.3f} "
        f"pre_events={len(pre)} obs_events={len(obs)}"
    )
    lines.append("segment mean_full mean_truncated mean_missing rel_missing max_missing")
    for a, b in segs:
        m = (grid >= a) & (grid < b)
        mean_full = float(np.mean(lam_full[m]))
        mean_trunc = float(np.mean(lam_trunc[m]))
        mean_missing = float(np.mean(missing[m]))
        rel = mean_missing / (mean_full + 1e-300)
        lines.append(
            f"{a:04.1f}-{b:04.1f} {mean_full:.6f} {mean_trunc:.6f} "
            f"{mean_missing:.6f} {rel:.4f} {float(np.max(missing[m])):.6f}"
        )
    comp_full = float(np.trapezoid(lam_full, grid))
    comp_trunc = float(np.trapezoid(lam_trunc, grid))
    lines.append(f"compensator_full={comp_full:.6f} compensator_truncated={comp_trunc:.6f} diff={comp_full-comp_trunc:.6f}")
    lines.append(
        "NODE verdict: truncating history creates a largest error near the left edge, but the "
        "compensator error is a global likelihood/residual error, not just a visual boundary blip."
    )
    return lines


def phase_series(kind: str, sigma: float, window: tuple[float, float], samples: int, rng) -> tuple[np.ndarray, np.ndarray]:
    t = np.linspace(window[0], window[1], samples)
    primes = first_primes(160)
    vals = []
    for tj in t:
        s = complex(float(sigma), float(tj))
        g = gamma_part(s)
        zp = dlog_zeta(s)
        if kind == "true":
            p = zp
        elif kind == "finite":
            p = dlog_finite(s, primes)
        elif kind == "random_phase":
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(zp) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(g + p)
    theta = np.unwrap(np.angle(np.asarray(vals, dtype=complex)))
    return t, theta


def run_lengths(mask: np.ndarray, dt: float) -> tuple[int, float, float]:
    lengths = []
    n = len(mask)
    i = 0
    while i < n:
        if not mask[i]:
            i += 1
            continue
        j = i
        while j < n and mask[j]:
            j += 1
        lengths.append((j - i) * dt)
        i = j
    if not lengths:
        return 0, 0.0, 0.0
    return len(lengths), float(np.mean(lengths)), float(np.max(lengths))


def phase_stats(t: np.ndarray, theta: np.ndarray, crop_frac: float = 0.10) -> dict[str, float]:
    dt = float(t[1] - t[0])
    dtheta = np.gradient(theta, t)
    energy = dtheta * dtheta
    total = float(np.trapezoid(energy, t))
    guard = max(2, int(crop_frac * len(t)))
    edge_energy = float(np.trapezoid(energy[:guard], t[:guard]) + np.trapezoid(energy[-guard:], t[-guard:]))
    sl = slice(guard, len(t) - guard)
    interior = float(np.trapezoid(energy[sl], t[sl]))
    gate = np.cos(theta) > 0.5
    gate_i = gate[sl]
    runs, mean_run, max_run = run_lengths(gate, dt)
    runs_i, mean_i, max_i = run_lengths(gate_i, dt)
    return {
        "h1_full": math.sqrt(total / (t[-1] - t[0])),
        "h1_interior": math.sqrt(interior / (t[sl][-1] - t[sl][0])),
        "edge_frac": edge_energy / (total + 1e-300),
        "runs_full": float(runs),
        "mean_run_full": mean_run,
        "max_run_full": max_run,
        "runs_interior": float(runs_i),
        "mean_run_interior": mean_i,
        "max_run_interior": max_i,
    }


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "The Hawkes compensator formula does not apply unchanged to C3; phase regularity is "
        "continuous in t and has no event-intensity offspring model. Direct transfer would be "
        "HT-blind."
    )
    lines.append(
        "Minimal transfer: keep the constraint that window-local statistics can be biased by "
        "history just outside the interval. For C3, test whether the phase-Sobolev gap survives "
        "guard-band deletion."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 20: NAME THE MISSING LEMMA")
    lines.append(
        "Missing lemma: C3 guard-band invariance. If the phase-Sobolev gap is intrinsic, then "
        "deleting a fixed-width edge guard should not erase the true-vs-control gap or invert the "
        "run-length relation."
    )
    rng = np.random.default_rng(2606215619)
    cases = [
        ("zero_strip", 0.50, (14.0, 84.0), "critical"),
        ("critical_low", 0.50, (100.0, 170.0), "critical"),
        ("critical_high", 0.50, (500.0, 570.0), "critical"),
        ("right_low", 1.30, (100.0, 170.0), "right"),
    ]
    lines.append(
        "case region kind h1_full h1_interior edge_frac runs_full runs_interior "
        "mean_run_i max_run_i"
    )
    stats_by_case: dict[str, dict[str, dict[str, float]]] = {}
    for label, sigma, window, region in cases:
        stats_by_case[label] = {}
        for kind in ["true", "finite", "random_phase"]:
            t, theta = phase_series(kind, sigma, window, 900, rng)
            st = phase_stats(t, theta)
            stats_by_case[label][kind] = st
            lines.append(
                f"{label:13s} {region:8s} {kind:12s} {st['h1_full']:.6f} {st['h1_interior']:.6f} "
                f"{st['edge_frac']:.4f} {int(st['runs_full']):03d} {int(st['runs_interior']):03d} "
                f"{st['mean_run_interior']:.4f} {st['max_run_interior']:.4f}"
            )
    lines.append("")
    lines.append("case full_gap(true-finite) interior_gap(true-finite) gap_retention true_edge_frac verdict")
    critical_survive = 0
    critical_total = 0
    right_collapse = 0
    right_total = 0
    for label, _sigma, _window, region in cases:
        true = stats_by_case[label]["true"]
        finite = stats_by_case[label]["finite"]
        full_gap = abs(true["h1_full"] - finite["h1_full"])
        int_gap = abs(true["h1_interior"] - finite["h1_interior"])
        retention = int_gap / (full_gap + 1e-300)
        if region == "critical":
            ok = retention > 0.70 and true["edge_frac"] < 0.35
            critical_survive += int(ok)
            critical_total += 1
        else:
            ok = int_gap < 0.03
            right_collapse += int(ok)
            right_total += 1
        lines.append(
            f"{label:13s} {full_gap:.6f} {int_gap:.6f} {retention:.4f} "
            f"{true['edge_frac']:.4f} {int(ok)}"
        )
    lines.append("")
    lines.append(f"CRITICAL_GUARD_BAND_GAP_SURVIVES {critical_survive}/{critical_total}")
    lines.append(f"RIGHT_GUARD_BAND_FINITE_COLLAPSE {right_collapse}/{right_total}")
    lines.append(
        "Interpretation: a positive result is not C3 itself. It only says the measured "
        "phase-Sobolev gap is not dominated by interval-edge energy in these windows. A failure "
        "would make C3 vulnerable to Hawkes-style missing-history artifacts."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: Hawkes edge correction -> C3")
    out.append(f"NODE: {NODE}")
    out.append(f"Standing-order target: {TARGET}")
    out.append(f"STEP 9 method: {METHOD}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
