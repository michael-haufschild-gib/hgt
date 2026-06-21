#!/usr/bin/env python3
"""STEP12 battery for Berry seam finite-resolution equalization."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("berry_resolution_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def mean_imbalance(base, kind, center, delta, samples, zeros, primes, seed_offset=0):
    vals = []
    phases = []
    for z in zeros:
        seed = 991400 + int(1000 * center) + int(1000 * delta) + samples + int(10 * z) + seed_offset + {
            "bare": 1,
            "xi": 2,
            "finite_xi": 3,
            "random_xi": 4,
        }[kind]
        imb, phase = base.lane_amplitude(kind, center, z, delta, samples, primes, np.random.default_rng(seed))
        vals.append(imb)
        phases.append(phase)
    return float(np.mean(vals)), float(np.max(vals)), float(np.mean(phases))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-kam-resolution-berry-seam.py")
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-kam-resolution-berry-seam.py").exists():
        module_path = "/tmp/2026-06-21-conway-kam-resolution-berry-seam.py"
    base = load_base(module_path)
    zeros = base.ZEROS
    primes = base.first_primes(args.prime_count)
    print("STEP12 battery: Berry seam finite-resolution equalization")
    print(f"zeros={len(zeros)} prime_count={args.prime_count}")
    print("A. all-method battery summary:")
    print("1 split: seam/off-seam/control; 2 attack false: finite/random; 3 reverse: off-seam; 4 viewpoint: bare vs completed;")
    print("5 visual: resolution ladder; 6 action: completion equalizes; 7 essentials: magnitude imbalance; 8 similar controls;")
    print("9 small cases: low samples; 10 extremes: delta sweep; 11 experiments: this battery; 12 invariant: zero imbalance;")
    print("13 monotone: off-center growth; 14 weaken: mean imbalance; 15 strengthen: max imbalance all zeros;")
    print("16 minimal counterexample: first five zeros; 17 representation: phase residual; 18 theorem-shape: FE symmetry;")
    print("19 fake proof: gamma+finite is enough (fails); 20 missing lemma: completed log-derivative lane magnitude symmetry;")
    print("21 dependency: true zeta plus gamma; 22 nearby false: center offsets; 23 boundary: seam vs off-seam.")
    print("\nB. resolution/delta stress")
    print("kind center delta samples mean_imb max_imb mean_phase")
    for center in [0.5, 0.52, 0.58]:
        for delta in [0.08, 0.16, 0.24]:
            for samples in [16, 24, 48, 96, 192, 384]:
                for kind in ["xi", "bare", "finite_xi"]:
                    mean_imb, max_imb, mean_phase = mean_imbalance(base, kind, center, delta, samples, zeros, primes)
                    print(f"{kind:9s} {center:.2f} {delta:.2f} {samples:5d} {mean_imb:10.7f} {max_imb:10.7f} {mean_phase:10.7f}")
    print("\nC. random control seed stress at seam")
    print("seed samples mean_imb max_imb")
    for seed_offset in range(10):
        mean_imb, max_imb, _ = mean_imbalance(base, "random_xi", 0.5, 0.16, 96, zeros, primes, 1000 * seed_offset)
        print(f"{seed_offset:4d} {96:5d} {mean_imb:10.7f} {max_imb:10.7f}")
    print("\nD. finite cutoff stress at seam")
    print("prime_count samples mean_imb max_imb")
    for n in [30, 80, 160, 320]:
        p = base.first_primes(n)
        mean_imb, max_imb, _ = mean_imbalance(base, "finite_xi", 0.5, 0.16, 96, zeros, p)
        print(f"{n:11d} {96:5d} {mean_imb:10.7f} {max_imb:10.7f}")


if __name__ == "__main__":
    main()
