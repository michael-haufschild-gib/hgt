#!/usr/bin/env python3
"""
R33 STEP 8/9 transfer to G-C10:
  Source-built faithful-index object.

NODE constraint:
  A Griffiths region is bounded by the clean critical point and the disordered
  critical point; observed global transition alone misses rare islands.

Target transfer:
  A finite source-built gate for a faithful index must not only show a global
  transition. It must expose rare local fake/off-line islands before global
  finite-gate failure, and smooth conductor-matched source controls should not
  produce the same islands.

Method #15, "strengthen the conjecture":
  strengthen "finite gate separates fakes" to a two-boundary requirement:
  rare local gate failure < global gate transition, with smooth controls quiet.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "2026-06-21-penrose-r30-jensen-coupled-defect-transition.py"
spec = importlib.util.spec_from_file_location("r30", SRC)
r30 = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(r30)

mp.mp.dps = 32


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        row = [i]
        for j, cb in enumerate(b, start=1):
            row.append(min(prev[j] + 1, row[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = row
    return prev[-1]


def quartet_factor(z: mp.mpf, gamma: float, a: float) -> mp.mpc:
    gg = mp.mpf(gamma)
    aa = mp.mpf(a)
    return (((z - gg) ** 2 + aa * aa) * ((z + gg) ** 2 + aa * aa)) / ((gg * gg + aa * aa) ** 2)


def smooth_lp_factor(z: mp.mpf, gamma: float, a: float) -> mp.mpc:
    # Zero-free Laguerre-Polya-type control, matched to the same center/scale.
    gg = mp.mpf(gamma)
    cc = mp.mpf(a * a) / (1 + gg * gg)
    return mp.e ** (-cc * (z - gg) ** 2)


def coeffs_for(kind: str, t: float, gamma: float, a: float) -> np.ndarray:
    tt = mp.mpf(t)
    if kind == "true":
        fun = r30.Xi
    elif kind == "fake_quartet":
        fun = lambda z: r30.Xi(z) * quartet_factor(z, gamma, a)
    elif kind == "smooth_control":
        fun = lambda z: r30.Xi(z) * smooth_lp_factor(z, gamma, a)
    else:
        raise ValueError(kind)
    tc = mp.taylor(fun, tt, 3)
    return np.array([float(mp.binomial(3, j) * mp.re(tc[j])) for j in range(4)], dtype=float)


def discrim_for(kind: str, t: float, gamma: float, a: float) -> float:
    c = coeffs_for(kind, t, gamma, a)
    return float(r30.cubic_discriminant(c[3], c[2], c[1], c[0]))


def longest_run(flags: np.ndarray) -> int:
    best = cur = 0
    for f in flags:
        if f:
            cur += 1
            best = max(best, cur)
        else:
            cur = 0
    return best


def scan(kind: str, gamma: float, a: float) -> tuple[int, int, float, float]:
    ts = np.linspace(gamma - 2.4, gamma + 2.4, 25)
    discs = np.array([discrim_for(kind, float(t), gamma, a) for t in ts])
    # Scale-free sign test with small tolerance against derivative noise.
    scale = np.nanmedian(np.abs(discs)) + 1e-300
    defects = discs < -1e-9 * scale
    return int(np.sum(defects)), longest_run(defects), float(np.min(discs / scale)), float(np.median(discs / scale))


def main() -> None:
    source = "griffiths_two_boundary_rare_region_gate"
    attempts = [
        "two_boundary_source_built_faithful_index_gate",
        "rare_region_finite_gate_fake_blindness",
        "clean_disordered_critical_index_interval",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:48s} distance={levenshtein(source, a)}")
    print(f"selected={min(attempts, key=lambda x: levenshtein(source, x))}")

    print("\nSTEP 9 method 15: strengthened two-boundary finite-gate test")
    print("cols: gamma a kind defects longest_run min_scaled_disc median_scaled_disc")
    gammas = [18.0, 37.0, 62.0]
    strengths = [0.00, 0.025, 0.050, 0.080, 0.120, 0.180]
    summary = []
    for gamma in gammas:
        rare_bound = None
        global_bound = None
        control_leaks = 0
        for a in strengths:
            rows = {}
            for kind in ["true", "smooth_control", "fake_quartet"]:
                defects, run, mn, med = scan(kind, gamma, a)
                rows[kind] = (defects, run, mn, med)
                print(f"{gamma:5.1f} {a:6.3f} {kind:15s} {defects:7d} {run:11d} {mn:16.6g} {med:18.6g}")
            if rare_bound is None and rows["fake_quartet"][0] > 0:
                rare_bound = a
            if global_bound is None and (rows["fake_quartet"][0] >= 5 or rows["fake_quartet"][1] >= 4):
                global_bound = a
            if rows["smooth_control"][0] > 0:
                control_leaks += 1
        summary.append((gamma, rare_bound, global_bound, control_leaks))

    print("\nTwo-boundary summary")
    print("gamma   rare_local_bound   global_transition_bound   smooth_control_leak_rows")
    for gamma, rare, glob, leaks in summary:
        print(f"{gamma:5.1f} {str(rare):>18s} {str(glob):>25s} {leaks:24d}")

    print("\nInterpretation")
    print(
        "A G-C10 finite gate should be judged by a rare-local bound and a global bound, "
        "not by one observed transition. If the rare bound is present for quartet fakes "
        "while smooth controls stay quiet, the gate has source-built fake sensitivity; "
        "if not, it fails the strengthened kill criterion."
    )


if __name__ == "__main__":
    main()
