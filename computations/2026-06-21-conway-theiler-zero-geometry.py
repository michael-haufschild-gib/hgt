#!/usr/bin/env python3
"""THE-MACHINE tick: Theiler windows -> zero geometry.

NODE:
  Ignoring Theiler windows when estimating dimensions, entropies, or neighbor
  statistics.

Consolidated target:
  6/32 Where the zeros live in the geometry.

STEP 9 method:
  20. Name the missing lemma.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


NODE = "Ignoring Theiler windows when estimating dimensions, entropies, or neighbor statistics"
TARGET = "6/32 Where the zeros live in the geometry"
METHOD = "20. Name the missing lemma"

TRANSFER_ATTEMPTS = [
    "zero geometry neighbor statistics need a Theiler exclusion in height",
    "source-neighborhood reconstruction must exclude same-trajectory temporal neighbors",
    "zeros live where source geometry survives temporal-neighbor exclusion",
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


def embed(x: np.ndarray, m: int = 3, tau: int = 2) -> np.ndarray:
    n = len(x) - (m - 1) * tau
    return np.column_stack([x[i * tau : i * tau + n] for i in range(m)])


def nn_stats(vecs: np.ndarray, future: np.ndarray, theiler: int) -> dict[str, float]:
    n = min(len(vecs), len(future))
    vecs = vecs[:n]
    future = future[:n]
    d2 = np.sum((vecs[:, None, :] - vecs[None, :, :]) ** 2, axis=2)
    idx = np.arange(n)
    d2[idx, idx] = np.inf
    if theiler > 0:
        close = np.abs(idx[:, None] - idx[None, :]) <= theiler
        d2[close] = np.inf
    nn = np.argmin(d2, axis=1)
    dist = np.sqrt(d2[idx, nn])
    sep = np.abs(idx - nn)
    a = future[:n]
    b = future[nn]
    aa = a - float(np.mean(a))
    bb = b - float(np.mean(b))
    corr = float(np.dot(aa, bb) / (np.linalg.norm(aa) * np.linalg.norm(bb) + 1e-300))
    return {
        "mean_dist": float(np.mean(dist[np.isfinite(dist)])),
        "median_sep": float(np.median(sep)),
        "leak_frac_10": float(np.mean(sep <= 10)),
        "pred_corr": corr,
    }


def lorenz_x(n: int = 7000, dt: float = 0.01) -> np.ndarray:
    x, y, z = 1.0, 1.0, 1.0
    xs = []
    for i in range(n + 1500):
        dx = 10.0 * (y - x)
        dy = x * (28.0 - z) - y
        dz = x * y - (8.0 / 3.0) * z
        x += dt * dx
        y += dt * dy
        z += dt * dz
        if i >= 1500:
            xs.append(x)
    arr = np.asarray(xs)
    return (arr - float(np.mean(arr))) / (float(np.std(arr)) + 1e-300)


def node_rows() -> list[str]:
    x = lorenz_x()
    y = x[::2]
    vec = embed(y, 3, 2)
    future = y[(3 - 1) * 2 + 1 : (3 - 1) * 2 + 1 + len(vec)]
    lines = ["STEP 5/6 NODE TEST: Theiler exclusion in delay reconstruction"]
    lines.append(
        "Constraint: nearest-neighbor estimates in reconstructed dynamics are inflated if "
        "temporally adjacent points are allowed as neighbors."
    )
    lines.append("theiler mean_dist median_sep leak_frac_sep_le_10 pred_corr")
    for w in [0, 5, 20, 60]:
        st = nn_stats(vec, future, w)
        lines.append(
            f"{w:03d} {st['mean_dist']:.6f} {st['median_sep']:.1f} {st['leak_frac_10']:.4f} {st['pred_corr']:.6f}"
        )
    lines.append(
        "NODE verdict: increasing the Theiler window removes near-time neighbor leakage and changes "
        "the neighbor-distance/prediction statistics."
    )
    return lines


def hgt_series(kind: str, sigma: float, window: tuple[float, float], samples: int, rng) -> tuple[np.ndarray, np.ndarray]:
    primes = first_primes(160)
    t = np.linspace(window[0], window[1], samples)
    vals = []
    for tj in t:
        s = complex(float(sigma), float(tj))
        a = gamma_part(s)
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
        vals.append(math.log1p(abs(a + p)))
    y = np.asarray(vals, dtype=float)
    return t, (y - float(np.mean(y))) / (float(np.std(y)) + 1e-300)


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Delay-reconstruction dimension formulas do not apply unchanged to zero geometry. "
        "The transfer keeps the constraint: nearest-neighbor source statistics must exclude "
        "trivial same-trajectory temporal neighbors."
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
        "Missing lemma: zero-neighbor Theiler invariance. A zero/source geometry neighbor statistic "
        "should retain its true-vs-control separation after excluding a temporal neighborhood in height."
    )
    rng = np.random.default_rng(2606216329)
    cases = [
        ("zero_strip", 0.50, (14.0, 84.0), "critical"),
        ("critical_low", 0.50, (100.0, 170.0), "critical"),
        ("critical_high", 0.50, (500.0, 570.0), "critical"),
        ("right_low", 1.30, (100.0, 170.0), "right"),
    ]
    lines.append("case region kind theiler mean_dist median_sep leak_frac pred_corr")
    summary = {}
    for label, sigma, window, region in cases:
        summary[label] = {}
        for kind in ["true", "finite", "random_phase"]:
            _t, y = hgt_series(kind, sigma, window, 820, rng)
            vec = embed(y, 3, 2)
            future = y[(3 - 1) * 2 + 1 : (3 - 1) * 2 + 1 + len(vec)]
            summary[label][kind] = {}
            for w in [0, 10, 30, 60]:
                st = nn_stats(vec, future, w)
                summary[label][kind][w] = st
                lines.append(
                    f"{label:13s} {region:8s} {kind:12s} {w:03d} {st['mean_dist']:.6f} "
                    f"{st['median_sep']:.1f} {st['leak_frac_10']:.4f} {st['pred_corr']:.6f}"
                )
    lines.append("")
    lines.append("case pred_gap_w0 pred_gap_w30 retention_w30 true_leak_w0 true_leak_w30 verdict")
    critical_ok = 0
    critical_total = 0
    right_ok = 0
    right_total = 0
    for label, _sigma, _window, region in cases:
        true0 = summary[label]["true"][0]["pred_corr"]
        fin0 = summary[label]["finite"][0]["pred_corr"]
        true30 = summary[label]["true"][30]["pred_corr"]
        fin30 = summary[label]["finite"][30]["pred_corr"]
        gap0 = abs(true0 - fin0)
        gap30 = abs(true30 - fin30)
        retention = gap30 / (gap0 + 1e-300)
        if region == "critical":
            ok = gap30 > 0.04 and retention > 0.35
            critical_ok += int(ok)
            critical_total += 1
        else:
            ok = gap30 < 0.03
            right_ok += int(ok)
            right_total += 1
        lines.append(
            f"{label:13s} {gap0:.6f} {gap30:.6f} {retention:.4f} "
            f"{summary[label]['true'][0]['leak_frac_10']:.4f} {summary[label]['true'][30]['leak_frac_10']:.4f} {int(ok)}"
        )
    lines.append("")
    lines.append(f"CRITICAL_THEILER_GAP_SURVIVES {critical_ok}/{critical_total}")
    lines.append(f"RIGHT_THEILER_FINITE_COLLAPSE {right_ok}/{right_total}")
    lines.append(
        "Interpretation: passing means the zero/source reconstruction statistic is not only "
        "successive-height continuity. Failure means the apparent geometry was temporal-neighbor leakage."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: Theiler windows -> zero geometry")
    out.append(f"NODE: {NODE}")
    out.append(f"Standing-order target: {TARGET}")
    out.append(f"STEP 9 method: {METHOD}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
