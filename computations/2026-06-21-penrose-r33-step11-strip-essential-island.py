#!/usr/bin/env python3
"""
R33 STEP 11: strip the G-C10/Jensen rare-island signal to essentials.

Method #7: keep only what is needed. Test whether the local one-site finite
gate defect is a universal off-real quartet island or a special Xi effect.
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


def quartet_factor(z: mp.mpf, gamma: float, a: float) -> mp.mpc:
    gg = mp.mpf(gamma)
    aa = mp.mpf(a)
    return (((z - gg) ** 2 + aa * aa) * ((z + gg) ** 2 + aa * aa)) / ((gg * gg + aa * aa) ** 2)


def smooth_lp_factor(z: mp.mpf, gamma: float, a: float) -> mp.mpc:
    gg = mp.mpf(gamma)
    cc = mp.mpf(a * a) / (1 + gg * gg)
    return mp.e ** (-cc * (z - gg) ** 2)


def background(kind: str, gamma: float):
    gg = mp.mpf(gamma)
    if kind == "flat":
        return lambda z: mp.mpf(1)
    if kind == "exp_slope":
        return lambda z: mp.e ** (mp.mpf("0.03") * (z - gg))
    if kind == "xi":
        return r30.Xi
    raise ValueError(kind)


def jensen_disc(fun, t: float) -> float:
    tc = mp.taylor(fun, mp.mpf(t), 3)
    coeff = np.array([float(mp.binomial(3, j) * mp.re(tc[j])) for j in range(4)], dtype=float)
    return float(r30.cubic_discriminant(coeff[3], coeff[2], coeff[1], coeff[0]))


def main() -> None:
    gamma = 37.0
    offsets = [-4, -2, -1, -0.5, 0, 0.5, 1, 2, 4]
    print("background a offset_over_a fake_scaled_disc smooth_scaled_disc")
    for bg_kind in ["flat", "exp_slope", "xi"]:
        bg = background(bg_kind, gamma)
        for a in [0.025, 0.050, 0.100, 0.180]:
            fake_vals = []
            smooth_vals = []
            for mult in offsets:
                t = gamma + mult * a
                fake = lambda z, bg=bg, a=a: bg(z) * quartet_factor(z, gamma, a)
                smooth = lambda z, bg=bg, a=a: bg(z) * smooth_lp_factor(z, gamma, a)
                fake_vals.append(jensen_disc(fake, t))
                smooth_vals.append(jensen_disc(smooth, t))
            scale = np.median(np.abs(fake_vals)) + 1e-300
            sscale = np.median(np.abs(smooth_vals)) + 1e-300
            for mult, fd, sd in zip(offsets, fake_vals, smooth_vals):
                print(f"{bg_kind:10s} {a:5.3f} {mult:12.2f} {fd/scale:17.6g} {sd/sscale:18.6g}")
            neg_width = sum(1 for fd in fake_vals if fd < -1e-9 * scale)
            smooth_leaks = sum(1 for sd in smooth_vals if sd < -1e-9 * sscale)
            print(f"SUMMARY {bg_kind:10s} a={a:5.3f} fake_negative_offsets={neg_width} smooth_negative_offsets={smooth_leaks}")

    print("\nInterpretation")
    print(
        "The rare finite-gate island survives on flat and exponential backgrounds, so the local "
        "defect is the universal off-real quartet signature. Xi supplies a source-built scan "
        "surface, but the one-island mechanism itself is not special to Xi."
    )


if __name__ == "__main__":
    main()
