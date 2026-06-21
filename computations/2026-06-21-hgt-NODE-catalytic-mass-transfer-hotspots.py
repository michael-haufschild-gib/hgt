#!/usr/bin/env python3
"""THE-MACHINE NODE test: mass transfer mimics catalytic hot spots.

NODE:
    Mass-transfer limitations that mimic intrinsic catalytic hot-spot activity.

Constraint tested:
    Observed local rate is not only intrinsic turnover. It is the series coupling
    of intrinsic reaction and transport supply. If transport varies spatially,
    apparent activity maps can identify transport-access hot spots as if they
    were intrinsically better catalytic sites.
"""

from __future__ import annotations

import argparse

import numpy as np


def smooth_random_field(n: int, rng: np.random.Generator, scale: float) -> np.ndarray:
    white = rng.normal(size=n)
    width = max(3, int(scale * n))
    x = np.arange(-3 * width, 3 * width + 1)
    kernel = np.exp(-0.5 * (x / width) ** 2)
    kernel /= kernel.sum()
    return np.convolve(white, kernel, mode="same")


def rates(k_intrinsic: np.ndarray, h_transport: np.ndarray, bulk: float = 1.0) -> tuple[np.ndarray, np.ndarray]:
    surface = h_transport * bulk / np.maximum(h_transport + k_intrinsic, 1e-300)
    rate = k_intrinsic * surface
    return surface, rate


def summarize(label: str, k: np.ndarray, h: np.ndarray) -> dict[str, float]:
    surface, rate = rates(k, h)
    apparent_k = rate  # scientist divides by bulk concentration and ignores surface depletion.
    top = apparent_k >= np.quantile(apparent_k, 0.90)
    return {
        "label": label,
        "rate_median": float(np.median(rate)),
        "surface_median": float(np.median(surface)),
        "apparent_top_true_k_median": float(np.median(k[top])),
        "apparent_top_h_median": float(np.median(h[top])),
        "corr_app_k": float(np.corrcoef(apparent_k, k)[0, 1]),
        "corr_app_h": float(np.corrcoef(apparent_k, h)[0, 1]),
        "top_h_enrichment": float(np.median(h[top]) / np.median(h)),
        "top_k_enrichment": float(np.median(k[top]) / np.median(k)),
        "mass_transfer_limited_frac": float(np.mean(h < k)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sites", type=int, default=600)
    args = parser.parse_args()

    rng = np.random.default_rng(20260621)
    n = args.sites
    base_k = np.ones(n)
    transport_field = np.exp(1.1 * smooth_random_field(n, rng, 0.025))
    intrinsic_field = np.exp(1.1 * smooth_random_field(n, rng, 0.025))

    cases = {
        "uniform_k_variable_transport": (base_k, transport_field),
        "variable_k_uniform_transport": (intrinsic_field, np.ones(n)),
        "variable_k_and_transport": (intrinsic_field, transport_field),
        "high_transport_low_k_control": (1.0 / np.sqrt(transport_field), transport_field),
        "uniform_no_transport_gradient": (base_k, np.ones(n)),
    }

    print("NODE: mass-transfer limitation can mimic intrinsic catalytic hot spots")
    print(f"sites={n}")
    print(
        "case rate_median surface_median corr_app_k corr_app_h top_k_enrichment "
        "top_h_enrichment mt_limited_frac top_k_median top_h_median"
    )
    for label, (k, h) in cases.items():
        row = summarize(label, k, h)
        print(
            f"{label:34s} {row['rate_median']:.6f} {row['surface_median']:.6f} "
            f"{row['corr_app_k']:.6f} {row['corr_app_h']:.6f} "
            f"{row['top_k_enrichment']:.6f} {row['top_h_enrichment']:.6f} "
            f"{row['mass_transfer_limited_frac']:.6f} "
            f"{row['apparent_top_true_k_median']:.6f} {row['apparent_top_h_median']:.6f}"
        )

    print("\nBoundary sweep: increase intrinsic turnover at fixed transport")
    print("k_scale rate_median surface_median apparent_gain mt_limited_frac")
    base_rate = None
    for k_scale in [0.1, 0.3, 1.0, 3.0, 10.0, 30.0]:
        k = k_scale * base_k
        surface, rate = rates(k, transport_field)
        if base_rate is None:
            base_rate = float(np.median(rate))
        print(
            f"{k_scale:7.2f} {np.median(rate):11.6f} {np.median(surface):14.6f} "
            f"{np.median(rate) / max(base_rate, 1e-300):13.6f} {np.mean(transport_field < k):15.6f}"
        )

    print(
        "\nInterpretation: the NODE is validated if apparent hot spots correlate with "
        "transport supply under uniform intrinsic activity, and if increasing intrinsic "
        "turnover saturates under mass-transfer limitation."
    )


if __name__ == "__main__":
    main()
