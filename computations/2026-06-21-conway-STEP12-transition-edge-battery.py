#!/usr/bin/env python3
"""Stress battery for transition-edge dynamics vs residence times."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_base():
    path = Path(__file__).with_name("2026-06-21-conway-transition-path-vs-residence.py")
    spec = importlib.util.spec_from_file_location("transition_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load base module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def row(ns, kind, sigma, window, samples, prime_count, threshold, band, seed):
    primes = ns.first_primes(prime_count)
    rng = np.random.default_rng(seed + int(100 * sigma) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
    vals = ns.trace(kind, sigma, window, samples, primes, rng)
    return ns.transition_edges(vals, threshold=threshold, band=band)


def fmt(label, r):
    norm = r["softness"] / max(1.0, r["median_run"])
    print(
        f"{label:44s} events={r['events']:.0f} occ={r['occupancy']:.3f} "
        f"medrun={r['median_run']:.2f} edge_width={r['edge_width']:.2f} "
        f"edge_slope={r['edge_slope']:.4f} softness={r['softness']:.2f} "
        f"soft_per_run={norm:.2f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=320)
    args = parser.parse_args()
    ns = load_base()
    windows = [(100.0, 170.0), (500.0, 570.0)]

    print("STEP12 battery: transition-edge softness")
    print(f"samples={args.samples}")

    print("\nA. sigma=0.5 true/finite/random, threshold=0 band=0.12")
    for window in windows:
        for kind in ["true", "finite", "random"]:
            fmt(f"{kind} window={window}", row(ns, kind, 0.5, window, args.samples, 160, 0.0, 0.12, 1000))

    print("\nB. finite prime-count stress at sigma=0.5")
    for n in [30, 80, 160, 240, 400]:
        vals = []
        for window in windows:
            vals.append(row(ns, "finite", 0.5, window, args.samples, n, 0.0, 0.12, 2000))
        print(
            f"N={n:3d} mean_softness={np.mean([v['softness'] for v in vals]):.2f} "
            f"mean_soft_per_run={np.mean([v['softness']/max(1.0,v['median_run']) for v in vals]):.2f} "
            f"mean_medrun={np.mean([v['median_run'] for v in vals]):.2f} "
            f"mean_events={np.mean([v['events'] for v in vals]):.1f}"
        )

    print("\nC. band sensitivity at sigma=0.5")
    for band in [0.08, 0.12, 0.20]:
        for kind in ["true", "finite", "random"]:
            vals = [row(ns, kind, 0.5, w, args.samples, 160, 0.0, band, 3000) for w in windows]
            print(
                f"band={band:.2f} {kind:6s} mean_softness={np.mean([v['softness'] for v in vals]):.2f} "
                f"mean_edge_width={np.mean([v['edge_width'] for v in vals]):.2f} "
                f"mean_edge_slope={np.mean([v['edge_slope'] for v in vals]):.4f}"
            )

    print("\nD. right-side collapse at sigma=1.2")
    for window in windows:
        for kind in ["true", "finite", "random"]:
            fmt(f"{kind} sigma=1.2 window={window}", row(ns, kind, 1.2, window, args.samples, 160, 0.0, 0.12, 4000))


if __name__ == "__main__":
    main()
