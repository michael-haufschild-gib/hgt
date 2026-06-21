#!/usr/bin/env python3
"""THE-MACHINE tick: catalog completeness -> The one object.

NODE:
  The dependence of seismicity statistics on catalog completeness.

Consolidated target:
  The one object: omega=d log xi, H=A+P, not scalar amplitude or either
  component alone.

STEP 9 method:
  1. Split it into subclaims.
"""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


NODE = "the dependence of seismicity statistics on catalog completeness"
TRANSFER_ATTEMPTS = [
    "the canonical one object depends on completeness of archimedean and prime catalogs",
    "incomplete A or P catalogs can make the wrong zeta transport object look canonical",
    "catalog completeness decides whether H=A+P is distinguished from scalar amplitude",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def fit_power_tail(samples: np.ndarray, xmin: float) -> float:
    x = samples[samples >= xmin]
    if len(x) < 5:
        return float("nan")
    return 1.0 + len(x) / np.sum(np.log(x / xmin))


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606212621)
    lines = ["STEP 6 NODE TEST: seismic catalog completeness bias"]
    lines.append(
        "Synthetic Gutenberg-Richter-like magnitudes are observed through "
        "different completeness thresholds Mc. Statistics below Mc are censored."
    )
    lines.append("Mc observed_fraction event_rate b_est mean_mag tail_alpha_est")
    n = 60000
    # Exponential magnitudes above M0; b=1 in base-10 GR means exponential
    # rate beta=b ln 10.
    m0 = 1.0
    beta = math.log(10.0)
    mags = m0 + rng.exponential(1 / beta, size=n)
    sizes = 10 ** mags
    for mc in [1.0, 1.5, 2.0, 2.5, 3.0]:
        obs = mags[mags >= mc]
        frac = len(obs) / n
        b_est = math.log10(math.e) / max(float(np.mean(obs - mc)), 1e-12)
        alpha = fit_power_tail(sizes[mags >= mc], 10 ** mc)
        lines.append(f"{mc:.1f} {frac:.5f} {len(obs):5d} {b_est:.4f} {float(np.mean(obs)):.4f} {alpha:.4f}")
    lines.append(
        "NODE verdict: event rate and mean magnitude are catalog-completeness "
        "dependent; the tail exponent is recoverable only when the threshold "
        "is correctly declared."
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


def phase_defect(a: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(a), abs(p)) + 1e-300) - math.log(abs(a + p) + 1e-300))


def collect_fields(sigmas: list[float], window: tuple[float, float], samples: int, primes: tuple[int, ...], rng) -> dict[str, np.ndarray]:
    out = {k: np.zeros((samples, len(sigmas)), dtype=float) for k in ["A", "P", "H", "finiteH", "randomH", "Delta"]}
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            a = gamma_part(s)
            p = dlog_zeta(s)
            fp = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(p) * complex(math.cos(theta), math.sin(theta))
            out["A"][j, i] = math.log1p(abs(a))
            out["P"][j, i] = math.log1p(abs(p))
            out["H"][j, i] = math.log1p(abs(a + p))
            out["finiteH"][j, i] = math.log1p(abs(a + fp))
            out["randomH"][j, i] = math.log1p(abs(a + rp))
            out["Delta"][j, i] = phase_defect(a, p)
    return out


def association_top_eig(events: np.ndarray) -> float:
    x = events.astype(float)
    p = np.mean(x, axis=0, keepdims=True)
    centered = x - p
    cov = centered.T @ centered / max(1, x.shape[0])
    sd = np.sqrt(np.diag(cov) + 1e-12)
    corr = cov / (sd[:, None] * sd[None, :])
    np.fill_diagonal(corr, 0.0)
    return float(np.linalg.eigvalsh(corr)[-1])


def transfer_rows() -> list[str]:
    rng = np.random.default_rng(2606212658)
    primes = first_primes(160)
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Catalog completeness formulas do not apply unchanged to HGT. The "
        "transfer changes catalog completeness to component completeness: A "
        "only, P only, completed H=A+P, finite-completed, and random-phase "
        "completed catalogs."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 1: SPLIT INTO SUBCLAIMS")
    lines.append("Subclaim A: component-incomplete catalogs change event rates.")
    lines.append("Subclaim B: component-incomplete catalogs change cross-lane association.")
    lines.append("Subclaim C: completed H should be distinguished from A/P/scalar catalogs only if the distinction survives thresholds and controls.")
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    fields = collect_fields(sigmas, (100.0, 170.0), 520, primes, rng)
    thresholds = {
        "H_q70": float(np.quantile(fields["H"], 0.70)),
        "H_q85": float(np.quantile(fields["H"], 0.85)),
        "Delta_q70": float(np.quantile(fields["Delta"], 0.70)),
    }
    lines.append("threshold catalog event_fraction lane_min lane_max assoc_top_eig")
    for label, threshold in thresholds.items():
        for catalog in ["A", "P", "H", "finiteH", "randomH", "Delta"]:
            ev = fields[catalog] > threshold
            lane_occ = np.mean(ev, axis=0)
            eig = association_top_eig(ev)
            lines.append(
                f"{label:9s} {catalog:7s} {float(np.mean(ev)):.4f} "
                f"{float(np.min(lane_occ)):.4f} {float(np.max(lane_occ)):.4f} {eig:.4f}"
            )
    lines.append(
        "\nProvisional verdict: if H looks canonical only under an H-chosen "
        "threshold but not under Delta or control thresholds, the finding is "
        "catalog-completeness bias rather than new one-object content."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: seismic catalog completeness -> The one object")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 1/32 The one object")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
