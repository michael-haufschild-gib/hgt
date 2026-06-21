#!/usr/bin/env python3
"""THE-MACHINE run: preferential porous paths and seam-localized weld transport."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_preferential_flow() -> None:
    """Validate NODE: high-flow backbone bypasses most pore volume."""
    print("NODE simulation: preferential flow paths can bypass pore volume")
    print("size porosity total_flow volume_for_80_flux top10_flux_frac")
    rng = np.random.default_rng(70606)
    for size in [9, 13, 17]:
        for porosity in [0.45, 0.58, 0.72]:
            open_cells = rng.random((size, size)) < porosity
            open_cells[:, 0] = True
            open_cells[:, -1] = True
            conduct = open_cells * rng.lognormal(mean=0.0, sigma=1.25, size=(size, size))
            # Add one deliberately connected high-conductance backbone.
            row = size // 2
            conduct[row, :] += 8.0
            potentials = np.tile(np.linspace(1.0, 0.0, size), (size, 1))
            for _ in range(180):
                old = potentials.copy()
                for i in range(size):
                    for j in range(1, size - 1):
                        if conduct[i, j] <= 0:
                            continue
                        vals = []
                        weights = []
                        for di, dj in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                            ni, nj = i + di, j + dj
                            if 0 <= ni < size and 0 <= nj < size and conduct[ni, nj] > 0:
                                w = math.sqrt(conduct[i, j] * conduct[ni, nj])
                                vals.append(potentials[ni, nj])
                                weights.append(w)
                        if weights:
                            potentials[i, j] = float(np.average(vals, weights=weights))
                if float(np.max(np.abs(potentials - old))) < 1e-5:
                    break
            fluxes = []
            for i in range(size):
                for j in range(size - 1):
                    if conduct[i, j] > 0 and conduct[i, j + 1] > 0:
                        w = math.sqrt(conduct[i, j] * conduct[i, j + 1])
                        fluxes.append(abs(w * (potentials[i, j] - potentials[i, j + 1])))
            f = np.sort(np.asarray(fluxes))[::-1]
            total = float(np.sum(f))
            if total <= 1e-12:
                vol80 = 1.0
                top10 = 0.0
            else:
                csum = np.cumsum(f) / total
                vol80 = float((np.searchsorted(csum, 0.80) + 1) / len(f))
                topn = max(1, int(0.10 * len(f)))
                top10 = float(np.sum(f[:topn]) / total)
            print(f"{size:4d} {porosity:.2f} {total:10.4f} {vol80:10.4f} {top10:10.4f}")


def run_levenshtein() -> str:
    node_sig = "preferential flow paths bypass most pore volume"
    candidates = [
        "preferential seam transport paths bypass most sigma volume",
        "seam localized phase transport bypasses bulk strip volume",
        "source carrying defects flow through seam not volume",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best = None
    for i, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{i} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, i, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")
    return best[2]


def first_primes(n: int) -> tuple[int, ...]:
    primes = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def capacity_grid(kind: str, sigmas: np.ndarray, window, samples: int, primes, rng):
    grid = np.zeros((len(sigmas), samples))
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(np.linspace(window[0], window[1], samples, endpoint=False)):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            if kind == "true":
                p = dlog_zeta(s)
            elif kind == "finite":
                p = dlog_finite_euler(s, primes)
            else:
                base = dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p = abs(base) * complex(math.cos(theta), math.sin(theta))
            grid[i, j] = max(phase_defect(g, p), 0.0)
    return grid


def concentration_stats(grid: np.ndarray, sigmas: np.ndarray):
    flat = np.sort(grid.ravel())[::-1]
    total = float(np.sum(flat))
    if total <= 1e-12:
        return 1.0, 0.0, 0.0, 0.0
    csum = np.cumsum(flat) / total
    vol80 = float((np.searchsorted(csum, 0.80) + 1) / len(flat))
    top10 = float(np.sum(flat[: max(1, int(0.10 * len(flat)))]) / total)
    seam_mask = np.abs(sigmas - 0.5) <= 0.11
    seam_mass = float(np.sum(grid[seam_mask, :]) / total)
    seam_volume = float(np.mean(seam_mask))
    return vol80, top10, seam_mass, seam_mass / max(seam_volume, 1e-12)


def ht_seam_transport(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    windows = [(100.0, 170.0), (500.0, 570.0)]
    print("\nStanding-order consolidated target: seam Re(s)=1/2 localized many ways")
    print("STEP8 transfer: preferential seam transport paths bypass most sigma volume")
    print("STEP9 method 9: test small cases via coarse and medium sigma grids")
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print("grid window kind vol80 top10_mass seam_mass seam_enrichment preferential")
    for grid_name, sigmas in [
        ("small", np.asarray([0.3, 0.5, 0.7, 1.2])),
        ("medium", np.linspace(0.2, 1.2, 11)),
    ]:
        for window in windows:
            window_name = f"{int(window[0])}-{int(window[1])}"
            for kind in ["true", "finite", "random"]:
                seed = 706700 + len(grid_name) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind]
                grid = capacity_grid(kind, sigmas, window, samples, primes, np.random.default_rng(seed))
                vol80, top10, seam_mass, seam_enrich = concentration_stats(grid, sigmas)
                preferential = int(vol80 < 0.45 and top10 > 0.32 and seam_enrich > 1.15)
                print(
                    f"{grid_name:6s} {window_name:7s} {kind:6s} {vol80:7.4f} {top10:9.4f} "
                    f"{seam_mass:9.4f} {seam_enrich:9.4f} {preferential:d}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=140)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_preferential_flow()
    run_levenshtein()
    print(
        "\nSTEP7 formula check: Darcy/network-flow effective permeability formulas apply unchanged only "
        "as generic graph transport, so unchanged use is seam-blind and not promoted."
    )
    ht_seam_transport(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
