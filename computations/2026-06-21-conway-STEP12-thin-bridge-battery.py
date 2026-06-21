#!/usr/bin/env python3
"""Stress battery for zero-shadow bridge connectivity."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_base():
    path = Path(__file__).with_name("2026-06-21-conway-thin-bridge-sampling.py")
    spec = importlib.util.spec_from_file_location("thin_bridge_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load base module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def mask_for(ns, kind, window, threshold, sigma_samples, t_samples, prime_count, seed):
    sigmas = np.linspace(0.2, 0.9, sigma_samples)
    ts = np.linspace(window[0], window[1], t_samples)
    primes = ns.first_primes(prime_count)
    rng = np.random.default_rng(seed + int(window[0]) + int(100 * threshold) + {"true": 1, "finite": 2, "random": 3}[kind])
    return ns.zero_shadow_mask(kind, sigmas, ts, primes, rng, threshold)


def st_line(ns, label, mask, p=0.8):
    st = ns.sampling_stress(mask, np.random.default_rng(1111), p=p, trials=100)
    print(
        f"{label:42s} occ={st['occupied']:.3f} full_comp={st['full_components']:.0f} "
        f"full_largest={st['full_largest']:.3f} span_sigma={st['full_span_sigma']:.0f} "
        f"span_t={st['full_span_t']:.0f} thin_cols={st['full_thin_cols']:.0f} "
        f"sample_p={p:.2f} sample_comp={st['sample_components']:.2f} "
        f"sample_span_sigma={st['sample_span_sigma']:.3f} sample_span_t={st['sample_span_t']:.3f} "
        f"sample_largest={st['sample_largest']:.3f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-samples", type=int, default=180)
    parser.add_argument("--sigma-samples", type=int, default=17)
    args = parser.parse_args()
    ns = load_base()
    windows = [(100.0, 170.0), (500.0, 570.0)]

    print("STEP12 battery: zero-shadow bridge connectivity")
    print(f"sigma_samples={args.sigma_samples} t_samples={args.t_samples}")

    print("\nA. prime-count stress, threshold=1.00")
    for n in [30, 80, 160, 240, 400]:
        for window in windows:
            st_line(ns, f"finite N={n:3d} window={window}", mask_for(ns, "finite", window, 1.00, args.sigma_samples, args.t_samples, n, 2000), p=0.8)

    print("\nB. true vs controls across thresholds")
    for threshold in [0.75, 1.00, 1.25]:
        for window in windows:
            for kind in ["true", "finite", "random"]:
                st_line(ns, f"{kind} threshold={threshold:.2f} window={window}", mask_for(ns, kind, window, threshold, args.sigma_samples, args.t_samples, 160, 3000), p=0.8)

    print("\nC. sampling-rate boundary for true threshold=1.00")
    for window in windows:
        mask = mask_for(ns, "true", window, 1.00, args.sigma_samples, args.t_samples, 160, 4000)
        for p in [0.60, 0.75, 0.90, 0.97]:
            st_line(ns, f"true window={window}", mask, p=p)


if __name__ == "__main__":
    main()
