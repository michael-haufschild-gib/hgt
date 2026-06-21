#!/usr/bin/env python3
"""Stress battery for the near-neutral phase-advantage candidate."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_base():
    path = Path(__file__).with_name("2026-06-21-conway-near-neutral-collapse.py")
    spec = importlib.util.spec_from_file_location("near_neutral_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load base module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def paired_adv(ns, sigma, window, samples, prime_count, control, seed_offset=0):
    primes = ns.first_primes(prime_count)
    true_vals = ns.trace("true", sigma, window, samples, primes, np.random.default_rng(101))
    rng = np.random.default_rng(700000 + int(100 * sigma) + int(window[0]) + seed_offset + {"finite": 2, "random": 3}[control])
    control_vals = ns.trace(control, sigma, window, samples, primes, rng)
    return true_vals - control_vals


def print_row(label, row):
    print(
        f"{label:40s} hidden_frac={row.hidden_frac:.3f} hidden_mean={row.hidden_mean:+.5f} "
        f"hidden_sum={row.hidden_sum:+.5f} hidden_pos={row.hidden_pos_frac:.3f} "
        f"visible_mean={row.visible_mean:+.5f} total_mean={row.total_mean:+.5f} "
        f"exp100={row.exp_hidden:.3f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=320)
    args = parser.parse_args()
    ns = load_base()
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    eps = 0.20

    print("STEP12 battery: near-neutral phase-advantage stress tests")
    print(f"samples={args.samples} eps={eps}")

    print("\nA. prime-count stress at sigma=0.7 against finite Euler")
    for n in [30, 80, 160, 240, 400]:
        rows = []
        for window in windows:
            adv = paired_adv(ns, 0.7, window, args.samples, n, "finite")
            rows.append(ns.hidden_advantage_row(adv, eps))
        print(
            f"N={n:3d} mean_hidden_frac={np.mean([r.hidden_frac for r in rows]):.3f} "
            f"mean_hidden_mean={np.mean([r.hidden_mean for r in rows]):+.5f} "
            f"mean_total={np.mean([r.total_mean for r in rows]):+.5f} "
            f"mean_hidden_pos={np.mean([r.hidden_pos_frac for r in rows]):.3f}"
        )

    print("\nB. sigma boundary against finite Euler, N=160")
    for sigma in [0.5, 0.6, 0.7, 0.8, 0.9, 1.2]:
        rows = []
        for window in windows:
            adv = paired_adv(ns, sigma, window, args.samples, 160, "finite")
            rows.append(ns.hidden_advantage_row(adv, eps))
        print(
            f"sigma={sigma:.1f} mean_hidden_frac={np.mean([r.hidden_frac for r in rows]):.3f} "
            f"mean_hidden_mean={np.mean([r.hidden_mean for r in rows]):+.5f} "
            f"mean_total={np.mean([r.total_mean for r in rows]):+.5f} "
            f"mean_visible={np.mean([r.visible_mean for r in rows]):+.5f} "
            f"mean_hidden_pos={np.mean([r.hidden_pos_frac for r in rows]):.3f}"
        )

    print("\nC. pairing and demeaning controls at sigma=0.7, N=160")
    for i, window in enumerate(windows):
        adv = paired_adv(ns, 0.7, window, args.samples, 160, "finite", seed_offset=i)
        print_row(f"paired window={window}", ns.hidden_advantage_row(adv, eps))
        shuffled = adv.copy()
        np.random.default_rng(9000 + i).shuffle(shuffled)
        print_row(f"shuffled-same-values window={window}", ns.hidden_advantage_row(shuffled, eps))
        demeaned = adv - float(np.mean(adv))
        print_row(f"demeaned window={window}", ns.hidden_advantage_row(demeaned, eps))

    print("\nD. random-phase boundary at sigma=0.7, amplitude-matched by construction")
    for window in windows:
        adv = paired_adv(ns, 0.7, window, args.samples, 160, "random")
        print_row(f"random window={window}", ns.hidden_advantage_row(adv, eps))


if __name__ == "__main__":
    main()
