#!/usr/bin/env python3
"""THE-MACHINE Step 11: invariant check for dissipative phase-flux assembly.

Method #12:
    Find an invariant.

If the cutoff tail ratio is fixed mostly by the leaky-integrator decay and the
continuous plateau is just integrated positive flux, the metaphor reduces to
model mechanics plus the old phase-defect amplitude distribution.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def load_step8_module():
    path = Path(__file__).with_name("2026-06-21-hgt-STEP8-dissipative-flux-phase-assembly.py")
    spec = importlib.util.spec_from_file_location("flux_step8", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def plateau(module, flux: np.ndarray, decay: float, cutoff_frac: float | None) -> float:
    threshold = float(np.quantile(flux, 0.50))
    state = module.maintained_state(flux, threshold, decay=decay, cutoff_frac=cutoff_frac)
    return float(np.mean(state[-60:]))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=180)
    args = parser.parse_args()
    module = load_step8_module()
    primes = module.first_primes(args.prime_count)
    rng = np.random.default_rng(260621121)
    print("STEP11 invariant check: leaky assembly is model-governed")
    print(f"samples={args.samples} prime_count={args.prime_count}")
    print("decay kind sigma window positive_flux_mean continuous cutoff_ratio")
    rows = []
    for decay in [0.025, 0.045, 0.080]:
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for window in [(100.0, 170.0), (500.0, 570.0)]:
                for kind in ["true", "finite", "random"]:
                    flux = module.flux_series(kind, sigma, window, args.samples, primes, rng)
                    threshold = float(np.quantile(flux, 0.50))
                    positive_mean = float(np.mean(np.maximum(0.0, flux - threshold)))
                    cont = plateau(module, flux, decay=decay, cutoff_frac=None)
                    cut = plateau(module, flux, decay=decay, cutoff_frac=0.55)
                    ratio = cut / max(cont, 1e-12)
                    rows.append((positive_mean, cont, ratio))
                    print(
                        f"{decay:.3f} {kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                        f"{positive_mean:.5f} {cont:.5f} {ratio:.5f}"
                    )
    arr = np.asarray(rows)
    corr = float(np.corrcoef(arr[:, 0], arr[:, 1])[0, 1])
    print(f"\nsummary plateau_vs_positive_flux_corr={corr:.5f} cutoff_ratio_min={float(arr[:,2].min()):.5f} cutoff_ratio_max={float(arr[:,2].max()):.5f}")


if __name__ == "__main__":
    main()
