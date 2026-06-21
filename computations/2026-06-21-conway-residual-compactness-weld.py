#!/usr/bin/env python3
"""THE-MACHINE tick: residual compactness -> The Weld.

NODE:
  Residual operators are not always compact in noncompact or incomplete settings.

Consolidated target:
  The Weld: H(s)=A(s)+P(s), archimedean-prime completed transport.

STEP 9 method:
  17. Change representation.
"""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


NODE = "residual operators not always being compact in noncompact or incomplete settings"

TRANSFER_ATTEMPTS = [
    "weld residual operators are not always compact in expanding t windows",
    "smoothing away weld residual can fail compactness on incomplete seam windows",
    "pointwise small weld remainders may have noncompact transport rank",
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


def effective_ranks(svals: np.ndarray) -> tuple[int, float]:
    s = np.asarray(svals, dtype=float)
    if s.size == 0 or s[0] <= 0:
        return 0, 0.0
    threshold_rank = int(np.sum(s / s[0] > 1e-2))
    p = s / np.sum(s)
    entropy_rank = float(np.exp(-np.sum(p * np.log(p + 1e-300))))
    return threshold_rank, entropy_rank


def node_convolution_rows() -> list[str]:
    lines = ["STEP 6 NODE TEST: smoothing residual compactness on compact vs expanding domains"]
    lines.append(
        "Gaussian convolution is smoothing. On a fixed compact interval its "
        "effective Fourier rank stabilizes as resolution increases. On an "
        "expanding periodic interval with fixed mesh, the number of significant "
        "singular values grows with volume, so the smoothing residual is not "
        "compact in the infinite-volume limit."
    )
    lines.append("case L dx n threshold_rank entropy_rank top_sv tail_sv")
    for case, length, dx in [
        ("compact_refine", 20.0, 0.20),
        ("compact_refine", 20.0, 0.10),
        ("compact_refine", 20.0, 0.05),
        ("expanding", 20.0, 0.10),
        ("expanding", 40.0, 0.10),
        ("expanding", 80.0, 0.10),
        ("expanding", 160.0, 0.10),
    ]:
        n = int(round(length / dx))
        freqs = np.fft.fftfreq(n, d=dx)
        # Periodic Gaussian convolution eigenvalues, normalized at frequency 0.
        svals = np.exp(-0.5 * (2 * math.pi * 0.35 * freqs) ** 2)
        svals = np.sort(np.abs(svals))[::-1]
        tr, er = effective_ranks(svals)
        lines.append(
            f"{case:14s} {length:6.1f} {dx:.2f} {n:5d} "
            f"{tr:4d} {er:8.3f} {svals[0]:.3f} {svals[-1]:.3e}"
        )
    lines.append("NODE verdict: smoothing/residual form does not imply compactness without a compact-domain hypothesis.")
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


def hankel(trace: np.ndarray, rows: int) -> np.ndarray:
    n = len(trace)
    cols = n - rows + 1
    return np.array([trace[i : i + cols] for i in range(rows)], dtype=float)


def weld_trace(kind: str, sigma: float, start: float, length: float, dt: float, primes: tuple[int, ...], rng) -> np.ndarray:
    values = []
    for t in np.arange(start, start + length, dt):
        s = complex(sigma, float(t))
        g = gamma_part(s)
        zp = dlog_zeta(s)
        if kind == "true":
            p = zp
        elif kind == "finite":
            p = dlog_finite(s, primes)
        elif kind == "random":
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(zp) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        values.append(phase_defect(g, p))
    return np.asarray(values, dtype=float)


def transfer_rows() -> list[str]:
    rng = np.random.default_rng(2606212219)
    primes = first_primes(160)
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Parametrix/residual compactness criteria do not apply unchanged to "
        "the Weld. The transfer uses the phase-weld defect trace and changes "
        "representation to a Hankel operator over expanding t-windows."
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
        "Pointwise trace -> Hankel operator. A compact-looking residual should "
        "have stable effective singular rank as the t-window grows."
    )
    lines.append(
        "sigma length kind mean_abs threshold_rank entropy_rank top_sv s10_ratio"
    )
    for sigma in [0.5, 0.8, 1.2]:
        for length in [40.0, 80.0, 160.0]:
            traces = {
                "true": weld_trace("true", sigma, 100.0, length, 0.25, primes, rng),
                "finite": weld_trace("finite", sigma, 100.0, length, 0.25, primes, rng),
                "random": weld_trace("random", sigma, 100.0, length, 0.25, primes, rng),
            }
            traces["true_minus_finite"] = traces["true"] - traces["finite"]
            traces["true_minus_random"] = traces["true"] - traces["random"]
            rows = min(64, len(next(iter(traces.values()))) // 3)
            for kind in ["true", "finite", "random", "true_minus_finite", "true_minus_random"]:
                x = traces[kind] - float(np.mean(traces[kind]))
                mat = hankel(x, rows)
                svals = np.linalg.svd(mat, compute_uv=False)
                tr, er = effective_ranks(svals)
                s10 = float(svals[min(9, len(svals) - 1)] / (svals[0] + 1e-300))
                lines.append(
                    f"{sigma:.1f} {length:6.1f} {kind:17s} {float(np.mean(np.abs(x))):.5f} "
                    f"{tr:4d} {er:8.3f} {svals[0]:.5g} {s10:.5f}"
                )
    lines.append(
        "\nProvisional verdict: promote only if true-minus-control residual rank "
        "grows in the critical/weld region but collapses on the right side; "
        "otherwise this is a generic noncompact-window warning."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: residual compactness -> The Weld")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 24/32 The Weld")
    out.extend(node_convolution_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
