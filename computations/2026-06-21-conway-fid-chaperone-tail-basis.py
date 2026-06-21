#!/usr/bin/env python3
"""Workflow pass: Hsp90 buffering/release -> FID tail basis test."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


mp.mp.dps = 100


def node_hsp90(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    variants = rng.normal(0.0, 1.0, size=5000)
    capacities = [1.0, 0.55, 0.25]
    print("NODE: Hsp90/chromatin effects can release buffered phenotypic variation")
    print("capacity expressed_frac phenotype_sd phenotype_q95")
    for cap in capacities:
        threshold = 1.7 * cap
        expressed = np.abs(variants) > threshold
        phenotype = np.where(expressed, variants, 0.12 * variants)
        print(
            f"{cap:.2f} {float(np.mean(expressed)):.3f} "
            f"{float(np.std(phenotype)):.3f} {float(np.quantile(np.abs(phenotype), 0.95)):.3f}"
        )
    print("action: buffer -> stress/release -> hidden variation becomes measurable")


def zeta_odd(n: int) -> mp.mpf:
    return mp.zeta(2 * n + 1)


def seq_value(kind: str, n: int) -> float:
    s = 2 * n + 1
    z = zeta_odd(n)
    if kind == "raw":
        return float(z)
    if kind == "tail":
        return float(z - 1)
    if kind == "two_scaled_tail":
        return float((z - 1) * mp.power(2, s))
    if kind == "three_scaled_after_two":
        return float((z - 1 - mp.power(2, -s)) * mp.power(3, s))
    if kind == "five_scaled_after_23":
        return float((z - 1 - mp.power(2, -s) - mp.power(3, -s)) * mp.power(5, s))
    raise ValueError(kind)


def hankel(kind: str, size: int) -> np.ndarray:
    vals = {n: seq_value(kind, n) for n in range(1, 2 * size + 1)}
    return np.array([[vals[i + j + 1] for j in range(size)] for i in range(size)], dtype=float)


def stats(kind: str, size: int) -> tuple[float, float, float, float]:
    h = hankel(kind, size)
    eig = np.linalg.eigvalsh(h)
    sign, logdet = np.linalg.slogdet(h)
    cond = eig[-1] / eig[0] if eig[0] > 0 else math.inf
    return float(eig[0]), float(eig[-1]), float(sign * logdet / math.log(10)), float(cond)


def transfer_fid() -> None:
    print()
    print("TRANSFER: ResearchNode #41 FID tail-stable Hankel basis/certificate")
    print("method #6 action: raw kappa buffers the nontrivial prime tail; peel/rescale to release it")
    print("kind size min_eig max_eig signed_log10det cond")
    kinds = ["raw", "tail", "two_scaled_tail", "three_scaled_after_two", "five_scaled_after_23"]
    for kind in kinds:
        for size in [3, 4, 5, 6, 7, 8]:
            mn, mx, logdet, cond = stats(kind, size)
            print(f"{kind:24s} {size:02d} {mn:+.4e} {mx:+.4e} {logdet:+.4f} {cond:.3e}")
        print()


def main() -> None:
    node_hsp90()
    transfer_fid()


if __name__ == "__main__":
    main()
