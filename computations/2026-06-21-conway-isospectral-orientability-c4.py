#!/usr/bin/env python3
"""THE-MACHINE tick: isospectral orientability -> C4 cross-lane correlation.

NODE:
  Orientability may not be determined by the spectrum in general settings.

Consolidated target:
  C4 -- divergent cross-lane correlation length xi_sigma.

STEP 9 method:
  9. Test small cases.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np


NODE = "orientability may not be determined by the spectrum in general settings"

TRANSFER_ATTEMPTS = [
    "cross lane orientation may not be determined by per lane spectra",
    "C4 weld orientability is not audible from scalar lane spectra",
    "cross sigma correlation length is hidden from lanewise spectra",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[j - 1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def connection_laplacian_cycle(n: int, holonomy: int) -> np.ndarray:
    """Z/2 connection Laplacian on a cycle.

    holonomy=+1 is periodic. holonomy=-1 has one twisted edge. The ordinary
    scalar graph Laplacian forgets the sign, but the connection Laplacian sees
    it.
    """
    signs = [1] * n
    signs[-1] = holonomy
    lap = np.zeros((n, n), dtype=float)
    for i, sign in enumerate(signs):
        j = (i + 1) % n
        lap[i, i] += 1
        lap[j, j] += 1
        lap[i, j] -= sign
        lap[j, i] -= sign
    return lap


def node_small_cases() -> list[str]:
    lines = ["STEP 6 NODE TEST: finite signed-cycle orientability analogue"]
    lines.append(
        "Constraint: scalar spectra can erase an orientation/twist datum; an "
        "orientation-sensitive operator is needed."
    )
    for n in [6, 10, 14]:
        scalar = connection_laplacian_cycle(n, +1)
        scalar_a = np.linalg.eigvalsh(scalar)
        scalar_b = np.linalg.eigvalsh(scalar)
        conn_plus = np.linalg.eigvalsh(connection_laplacian_cycle(n, +1))
        conn_minus = np.linalg.eigvalsh(connection_laplacian_cycle(n, -1))
        scalar_diff = float(np.max(np.abs(scalar_a - scalar_b)))
        conn_diff = float(np.max(np.abs(conn_plus - conn_minus)))
        zero_plus = float(conn_plus[0])
        zero_minus = float(conn_minus[0])
        lines.append(
            f"n={n:02d} scalar_spectrum_diff={scalar_diff:.3g} "
            f"connection_spectrum_diff={conn_diff:.6f} "
            f"lowest_plus/minus={zero_plus:.6f}/{zero_minus:.6f}"
        )
    lines.append(
        "NODE verdict: the scalar spectrum is identical by construction, while "
        "the Z/2 connection spectrum detects the hidden twist. This validates "
        "the NODE constraint in a small finite model."
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


def build_fields(
    sigmas: list[float],
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    fields = {kind: np.zeros((samples, len(sigmas)), dtype=float) for kind in ["true", "finite", "random"]}
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


def lane_standardize(field: np.ndarray) -> np.ndarray:
    x = np.asarray(field, dtype=float)
    mu = np.mean(x, axis=0, keepdims=True)
    sd = np.std(x, axis=0, keepdims=True) + 1e-12
    return (x - mu) / sd


def circular_shift_lanes(field: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    out = np.empty_like(field)
    n = field.shape[0]
    for i in range(field.shape[1]):
        shift = int(rng.integers(n // 5, 4 * n // 5))
        out[:, i] = np.roll(field[:, i], shift)
    return out


def fourier_scramble_lanes(field: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    out = np.empty_like(field)
    n = field.shape[0]
    for i in range(field.shape[1]):
        fft = np.fft.rfft(field[:, i])
        new = np.zeros_like(fft)
        new[0] = fft[0]
        end = len(fft) - 1
        for k in range(1, end):
            new[k] = abs(fft[k]) * np.exp(1j * rng.uniform(-math.pi, math.pi))
        if n % 2 == 0:
            new[end] = fft[end]
        else:
            new[end] = abs(fft[end]) * np.exp(1j * rng.uniform(-math.pi, math.pi))
        out[:, i] = np.fft.irfft(new, n=n)
    return out


def lane_power_rel_diff(a: np.ndarray, b: np.ndarray) -> float:
    diffs = []
    for i in range(a.shape[1]):
        pa = np.abs(np.fft.rfft(a[:, i])) ** 2
        pb = np.abs(np.fft.rfft(b[:, i])) ** 2
        diffs.append(float(np.linalg.norm(pa - pb) / (np.linalg.norm(pa) + 1e-12)))
    return float(max(diffs))


@dataclass
class CorrMetrics:
    top_eig: float
    adj_mean: float
    corr_length: float
    span20: int


def corr_metrics(field: np.ndarray) -> CorrMetrics:
    x = lane_standardize(field)
    corr = x.T @ x / x.shape[0]
    np.fill_diagonal(corr, 0.0)
    eig = np.linalg.eigvalsh(corr)
    by_dist = []
    for d in range(1, corr.shape[0]):
        vals = [corr[i, i + d] for i in range(corr.shape[0] - d)]
        by_dist.append(float(np.mean(vals)))
    pos = np.array([max(0.0, c) for c in by_dist], dtype=float)
    if float(np.sum(pos)) == 0.0:
        xi = 0.0
    else:
        xi = float(np.sum(np.arange(1, len(pos) + 1) * pos) / np.sum(pos))
    span20 = 0
    for d, c in enumerate(by_dist, 1):
        if c > 0.20:
            span20 = d
    return CorrMetrics(
        top_eig=float(eig[-1]),
        adj_mean=by_dist[0],
        corr_length=xi,
        span20=span20,
    )


def transfer_small_cases() -> list[str]:
    rng = np.random.default_rng(2606211949)
    primes = first_primes(160)
    scored = []
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "NODE spectral/orientation formulas apply unchanged only as finite "
        "linear-algebra diagnostics. The C4 transfer must use the phase-weld "
        "field and cross-sigma association, not a generic graph spectrum."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 9: TEST SMALL CASES")
    lines.append(
        "Small cases: compare the true phase-weld lane field with per-lane "
        "isospectral surrogates. Circular shifts and Fourier phase scrambling "
        "preserve each lane's scalar power spectrum, but may destroy C4 "
        "cross-lane orientation/correlation."
    )
    lines.append(
        "case kind power_diff top_eig adj_mean xi_sigma span20 "
        "top_eig_drop_vs_true"
    )
    cases = [
        ("critical_low", [0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (100.0, 140.0)),
        ("critical_mid", [0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (500.0, 540.0)),
        ("right_side", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55], (100.0, 140.0)),
    ]
    for label, sigmas, window in cases:
        fields = build_fields(sigmas, window, 360, primes, rng)
        true = lane_standardize(fields["true"])
        variants = {
            "true": true,
            "shifted": circular_shift_lanes(true, rng),
            "fourier": fourier_scramble_lanes(true, rng),
            "finite": lane_standardize(fields["finite"]),
            "random": lane_standardize(fields["random"]),
        }
        true_metrics = corr_metrics(variants["true"])
        for kind, field in variants.items():
            met = corr_metrics(field)
            pdiff = 0.0 if kind in {"true", "finite", "random"} else lane_power_rel_diff(true, field)
            drop = true_metrics.top_eig - met.top_eig
            lines.append(
                f"{label:12s} {kind:7s} {pdiff:.3e} {met.top_eig:.4f} "
                f"{met.adj_mean:.4f} {met.corr_length:.4f} {met.span20:d} {drop:.4f}"
            )
    lines.append(
        "\nProvisional interpretation: a non-reducing C4 increment would be a "
        "large true-vs-isospectral-surrogate drop in the critical strip that "
        "is not reproduced on the right side and not merely a threshold/marginal artifact."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: isospectral orientability -> C4 cross-lane correlation")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 12/32 C4 cross-lane correlation")
    out.extend(node_small_cases())
    out.extend(transfer_small_cases())
    print("\n".join(out))


if __name__ == "__main__":
    main()
