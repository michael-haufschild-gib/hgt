#!/usr/bin/env python3
"""THE-MACHINE Step 11: action test for phase support irreversibility.

Method #6:
    Ask what action is happening.

Hypothesis under attack:
    The reverse-support lambda is not an HT-native irreversibility measure; it
    is mostly the action of transporting/misaligning high phase-support under
    mirror plus time reversal. Circular-shift nulls test this directly.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def load_step8_module():
    path = Path(__file__).with_name("2026-06-21-hgt-STEP8-absolute-irreversibility-phase-support.py")
    spec = importlib.util.spec_from_file_location("support_step8", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=180)
    parser.add_argument("--shifts", type=int, default=160)
    args = parser.parse_args()
    module = load_step8_module()
    primes = module.first_primes(args.prime_count)
    rng = np.random.default_rng(260621106)
    print("STEP11 action test: mirror/time-reversal support transport vs circular-shift null")
    print(f"samples={args.samples} prime_count={args.prime_count} shifts={args.shifts}")
    print("kind sigma mirror window q observed_lambda null_mean null_q05 null_q95 z_like outside_null")
    for kind in ["true", "finite", "random"]:
        for sigma in [0.2, 0.3, 0.4]:
            mirror = 1.0 - sigma
            for window in [(100.0, 170.0), (500.0, 570.0)]:
                fwd = module.values(kind, sigma, window, args.samples, primes, rng)
                rev = module.values(kind, mirror, window, args.samples, primes, rng)[::-1]
                for q in [0.50, 0.70, 0.85]:
                    obs = module.support_lambda(fwd, rev, q)["lambda"]
                    null = []
                    for _ in range(args.shifts):
                        shift = int(rng.integers(0, len(rev)))
                        null.append(module.support_lambda(fwd, np.roll(rev, shift), q)["lambda"])
                    arr = np.asarray(null, dtype=float)
                    mu = float(np.mean(arr))
                    sd = float(np.std(arr) + 1e-12)
                    q05, q95 = np.quantile(arr, [0.05, 0.95])
                    outside = int(obs < q05 or obs > q95)
                    print(
                        f"{kind:6s} {sigma:.1f} {mirror:.1f} [{window[0]:.0f},{window[1]:.0f}] {q:.2f} "
                        f"{obs:.4f} {mu:.4f} {float(q05):.4f} {float(q95):.4f} "
                        f"{(obs-mu)/sd:+.2f} {outside}"
                    )


if __name__ == "__main__":
    main()
