#!/usr/bin/env python3
"""STEP12 battery for phase-regulated high-defect run dissolution."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("desquamation_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def trace_windows(base, kind: str, sigma: float, windows, samples: int, primes, rng):
    rows = []
    for window in windows:
        for t in np.linspace(window[0], window[1], samples):
            s = complex(float(sigma), float(t))
            g = base.gamma_part(s)
            if kind == "true":
                p = base.dlog_zeta(s)
            elif kind == "finite":
                p = base.dlog_finite_euler(s, primes)
            else:
                z = base.dlog_zeta(s)
                theta = rng.uniform(-np.pi, np.pi)
                p = abs(z) * complex(np.cos(theta), np.sin(theta))
            rows.append(base.observables(g, p))
        rows.append((float("nan"), float("nan"), float("nan")))
    return np.asarray(rows)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-desquamation-link-dissolution.py")
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-desquamation-link-dissolution.py").exists():
        module_path = "/tmp/2026-06-21-conway-desquamation-link-dissolution.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    window_sets = {
        "combined": [(100.0, 170.0), (500.0, 570.0)],
        "low": [(100.0, 170.0)],
        "high": [(500.0, 570.0)],
    }
    print("STEP12 battery: high-defect exit dissolution mechanism")
    print(f"samples_per_window={args.samples} prime_count={args.prime_count}")
    print("window threshold kind sigma exits phase_fraction phase_dominant mean_link_drop")
    for window_name, windows in window_sets.items():
        for threshold in [0.8, 1.0, 1.2, 1.5]:
            for sigma in [0.3, 0.5, 1.2]:
                for kind in ["true", "finite", "random"]:
                    rng = np.random.default_rng(1610000 + len(window_name) + int(1000 * threshold) + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
                    rows = trace_windows(base, kind, sigma, windows, args.samples, primes, rng)
                    exits, phase_frac, phase_dom, drop = base.exit_mechanisms(rows, threshold)
                    print(f"{window_name:8s} {threshold:.1f} {kind:6s} {sigma:.1f} {exits:4d} {phase_frac:.4f} {phase_dom:.4f} {drop:.4f}")


if __name__ == "__main__":
    main()
