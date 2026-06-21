#!/usr/bin/env python3
"""STEP11 viewpoint change: boundary flow for almost-invariant weld sets."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("almost_invariant_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def transitions(mask: np.ndarray):
    a = mask[:-1]
    b = mask[1:]
    in_count = max(int(np.sum(a)), 1)
    out_count = max(int(np.sum(~a)), 1)
    p_in_in = float(np.sum(a & b) / in_count)
    p_in_out = float(np.sum(a & ~b) / in_count)
    p_out_in = float(np.sum(~a & b) / out_count)
    flow_balance = p_out_in - p_in_out
    return p_in_in, p_in_out, p_out_in, flow_balance


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-almost-invariant-weld-retention.py")
    parser.add_argument("--samples", type=int, default=520)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-almost-invariant-weld-retention.py").exists():
        module_path = "/tmp/2026-06-21-conway-almost-invariant-weld-retention.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    print("STEP11 viewpoint change: boundary leakage/re-entry, not just retention")
    print(f"samples_per_window={args.samples} prime_count={args.prime_count}")
    print("window kind sigma threshold p_in_in p_in_out p_out_in balance exchange_layer")
    for window in [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]:
        window_name = f"{int(window[0])}-{int(window[1])}"
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for kind in ["true", "finite", "random"]:
                seed = 205900 + int(window[0]) + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind]
                vals = base.trace(kind, sigma, window, args.samples, primes, np.random.default_rng(seed))
                threshold = float(np.quantile(vals, 0.70))
                mask = vals >= threshold
                p_in_in, p_in_out, p_out_in, balance = transitions(mask)
                # Exchange layer: high short retention, but non-negligible two-way boundary flow.
                exchange = int(p_in_in > 0.62 and p_in_out > 0.10 and p_out_in > 0.04)
                print(
                    f"{window_name:7s} {kind:6s} {sigma:.1f} {threshold:9.4f} "
                    f"{p_in_in:7.3f} {p_in_out:8.3f} {p_out_in:8.3f} {balance:8.3f} {exchange:d}"
                )


if __name__ == "__main__":
    main()
