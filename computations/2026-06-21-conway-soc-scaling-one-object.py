#!/usr/bin/env python3
"""THE-MACHINE tick: SOC multiple scaling relations -> The one object.

NODE:
  Multiple scaling relations should be checked together, not just one fitted exponent.

Consolidated target:
  The one object -- H = A + P, completed logarithmic transport connection.

STEP 9 method:
  6. Ask what action is happening.
"""

from __future__ import annotations

from collections import deque
import math
import runpy

import numpy as np


NODE = "multiple scaling relations should be checked together not just one fitted exponent"

TRANSFER_ATTEMPTS = [
    "the one object must pass joint event size duration scaling not one exponent",
    "H equals A plus P should be tested by compatible scaling relations together",
    "single scalar exponent cannot choose the completed object H A plus P",
]

BASE = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
first_primes = BASE["first_primes"]
gamma_part = BASE["gamma_part"]
dlog_zeta = BASE["dlog_zeta"]
dlog_finite = BASE["dlog_finite"]
phase_defect = BASE["phase_defect"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def fit_ccdf_alpha(x: np.ndarray) -> float:
    x = np.asarray(x, dtype=float)
    x = x[x >= 1]
    if len(x) < 10 or np.max(x) <= np.min(x):
        return float("nan")
    cutoff = np.quantile(x, 0.35)
    vals = np.sort(x[x >= cutoff])
    unique = np.unique(vals)
    if len(unique) < 4:
        return float("nan")
    ccdf = np.array([np.mean(vals >= u) for u in unique], dtype=float)
    mask = (unique > 0) & (ccdf > 0)
    slope, _ = np.polyfit(np.log(unique[mask]), np.log(ccdf[mask]), 1)
    return float(-slope)


def fit_gamma(sizes: np.ndarray, durations: np.ndarray) -> float:
    mask = (sizes > 1) & (durations > 1)
    if np.sum(mask) < 10 or len(np.unique(durations[mask])) < 4:
        return float("nan")
    slope, _ = np.polyfit(np.log(durations[mask]), np.log(sizes[mask]), 1)
    return float(slope)


def scaling_metrics(sizes: np.ndarray, durations: np.ndarray) -> tuple[float, float, float, float]:
    alpha_s = fit_ccdf_alpha(sizes)
    alpha_t = fit_ccdf_alpha(durations)
    gamma = fit_gamma(sizes, durations)
    if any(math.isnan(v) for v in [alpha_s, alpha_t, gamma]):
        residual = float("nan")
    else:
        residual = abs(alpha_t - gamma * alpha_s)
    return alpha_s, alpha_t, gamma, residual


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606215021)
    n = 6000
    gamma_true = 1.55
    durations = (1.0 + rng.pareto(1.2, size=n)).clip(1, 400)
    sizes_good = durations**gamma_true * np.exp(rng.normal(scale=0.25, size=n))
    sizes_fake = np.sort(sizes_good).copy()
    rng.shuffle(sizes_fake)
    alpha_s_good, alpha_t_good, gamma_good, resid_good = scaling_metrics(sizes_good, durations)
    alpha_s_fake, alpha_t_fake, gamma_fake, resid_fake = scaling_metrics(sizes_fake, durations)
    lines = ["STEP 6 NODE TEST: one exponent can be faked while scaling relations fail"]
    lines.append(
        "Good data and fake data share the same size sample. The fake shuffles sizes against durations, "
        "preserving the size exponent but breaking the duration relation."
    )
    lines.append("case alpha_size alpha_duration gamma_size_vs_duration scaling_residual")
    lines.append(f"consistent {alpha_s_good:.4f} {alpha_t_good:.4f} {gamma_good:.4f} {resid_good:.4f}")
    lines.append(f"shuffled   {alpha_s_fake:.4f} {alpha_t_fake:.4f} {gamma_fake:.4f} {resid_fake:.4f}")
    lines.append(
        "NODE verdict: a single fitted exponent is insufficient; the action is compatibility "
        "among several scaling relations."
    )
    return lines


def connected_components(binary: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    rows, cols = binary.shape
    seen = np.zeros_like(binary, dtype=bool)
    sizes = []
    durations = []
    spans = []
    for r in range(rows):
        for c in range(cols):
            if not binary[r, c] or seen[r, c]:
                continue
            q = deque([(r, c)])
            seen[r, c] = True
            cells = []
            while q:
                x, y = q.popleft()
                cells.append((x, y))
                for dx, dy in [(1, 0), (-1, 0), (0, 1), (0, -1)]:
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < rows and 0 <= ny < cols and binary[nx, ny] and not seen[nx, ny]:
                        seen[nx, ny] = True
                        q.append((nx, ny))
            arr = np.array(cells)
            sizes.append(len(cells))
            spans.append(int(arr[:, 0].max() - arr[:, 0].min() + 1))
            durations.append(int(arr[:, 1].max() - arr[:, 1].min() + 1))
    return np.array(sizes), np.array(durations), np.array(spans)


def build_fields(sigmas, window, samples, primes, rng):
    fields = {k: np.zeros((len(sigmas), samples), dtype=float) for k in ["A", "P", "H", "Delta", "finiteH", "randomH"]}
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            a = gamma_part(s)
            p = dlog_zeta(s)
            pf = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            pr = abs(p) * complex(math.cos(theta), math.sin(theta))
            fields["A"][i, j] = math.log1p(abs(a))
            fields["P"][i, j] = math.log1p(abs(p))
            fields["H"][i, j] = math.log1p(abs(a + p))
            fields["Delta"][i, j] = phase_defect(a, p)
            fields["finiteH"][i, j] = math.log1p(abs(a + pf))
            fields["randomH"][i, j] = math.log1p(abs(a + pr))
    return fields


def collect_component_stats(field: np.ndarray, quantiles: list[float]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    all_sizes = []
    all_durations = []
    all_spans = []
    for q in quantiles:
        threshold = float(np.quantile(field, q))
        sizes, durations, spans = connected_components(field >= threshold)
        all_sizes.extend(sizes.tolist())
        all_durations.extend(durations.tolist())
        all_spans.extend(spans.tolist())
    return np.array(all_sizes), np.array(all_durations), np.array(all_spans)


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "SOC exponent formulas do not apply unchanged to HGT. The transfer keeps the NODE constraint: "
        "a candidate one-object field should be judged by compatibility among event-component scaling "
        "relations, not by one exponent or raw event count."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 6: ASK WHAT ACTION IS HAPPENING")
    lines.append("Action: extract event components, fit size and duration tails, then check alpha_T ≈ gamma alpha_S.")

    rng = np.random.default_rng(2606215111)
    primes = first_primes(160)
    sigmas = np.linspace(0.20, 0.90, 9)
    cases = [
        ("zero_low", (14.0, 84.0)),
        ("critical_low", (100.0, 170.0)),
        ("critical_high", (500.0, 570.0)),
    ]
    quantiles = [0.70, 0.75, 0.80, 0.85, 0.90]
    lines.append("case object components alpha_size alpha_duration gamma residual span_mean event_cells")
    for label, window in cases:
        fields = build_fields(sigmas, window, 360, primes, rng)
        for name, field in fields.items():
            sizes, durations, spans = collect_component_stats(field, quantiles)
            alpha_s, alpha_t, gamma, residual = scaling_metrics(sizes, durations)
            event_cells = int(np.sum(sizes))
            span_mean = float(np.mean(spans)) if len(spans) else float("nan")
            lines.append(
                f"{label:13s} {name:8s} {len(sizes):04d} {alpha_s:.4f} {alpha_t:.4f} "
                f"{gamma:.4f} {residual:.4f} {span_mean:.3f} {event_cells:05d}"
            )
    lines.append(
        "\nProvisional interpretation: a low residual is only meaningful if it selects H over A/P/finite/random "
        "and persists across windows. Otherwise multiple-scaling checks are instrument hygiene, not a one-object theorem."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: SOC multiple scaling relations -> The one object")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 1/32 The one object")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
