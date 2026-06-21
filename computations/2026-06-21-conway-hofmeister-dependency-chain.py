#!/usr/bin/env python3
"""STEP11 dependency-chain test for endpoint ranking transfer."""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("hofmeister_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def pair_agreement(a: np.ndarray, b: np.ndarray) -> float:
    total = 0
    agree = 0
    for i in range(len(a)):
        for j in range(i + 1, len(a)):
            da = a[i] - a[j]
            db = b[i] - b[j]
            if abs(da) < 1e-12 or abs(db) < 1e-12:
                continue
            total += 1
            agree += int(da * db > 0)
    return agree / total if total else 0.0


def endpoint_values(base, g: np.ndarray, p: np.ndarray, threshold: float):
    perturbations = [(lam, phi) for lam in [0.45, 0.70, 1.00, 1.35] for phi in [-1.30, -0.45, 0.45, 1.30]]
    surface = []
    phase = []
    run = []
    var = []
    for lam, phi in perturbations:
        z = lam * complex(math.cos(phi), math.sin(phi)) * p
        defect = base.phase_defect(g, z)
        mask = defect > threshold
        surface.append(float(np.mean(np.log(np.abs(g + z) + 1e-300))))
        phase.append(float(np.mean(mask)))
        run.append(base.mean_run(mask))
        var.append(float(np.var(defect)))
    return [np.asarray(x) for x in [surface, phase, run, var]]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-hofmeister-endpoint-transfer.py")
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=1.0)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-hofmeister-endpoint-transfer.py").exists():
        module_path = "/tmp/2026-06-21-conway-hofmeister-endpoint-transfer.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    print("STEP11 dependency chain: surface -> phase -> run -> variance")
    print(f"samples_per_window={args.samples} prime_count={args.prime_count} threshold={args.threshold:.3f}")
    print("kind sigma surface_phase phase_run run_variance all_adjacent_mean surface_variance")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(671000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            g, p = base.traces(kind, sigma, args.samples, primes, rng)
            surface, phase, run, var = endpoint_values(base, g, p, args.threshold)
            a = pair_agreement(surface, phase)
            b = pair_agreement(phase, run)
            c = pair_agreement(run, var)
            d = pair_agreement(surface, var)
            print(f"{kind:6s} {sigma:.1f} {a:.3f} {b:.3f} {c:.3f} {(a+b+c)/3:.3f} {d:.3f}")


if __name__ == "__main__":
    main()
