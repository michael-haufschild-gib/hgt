#!/usr/bin/env python3
"""
Attempt 5 NODE experiment.

NODE: hidden anisotropy of rectangular/grid-oriented finite averaging windows.

Constraint tested:
  A spatially isotropic filter must attenuate plane waves by a factor depending
  only on |k|.  A rectangular box filter has direction-dependent Fourier
  response even when |k| is fixed.
"""

from __future__ import annotations

import math

import numpy as np


def sinc(x: float) -> float:
    if abs(x) < 1e-12:
        return 1.0
    return math.sin(x) / x


def box_response(kx: float, ky: float, width_x: float, width_y: float) -> float:
    return abs(sinc(0.5 * width_x * kx) * sinc(0.5 * width_y * ky))


def gaussian_response(kx: float, ky: float, sigma: float) -> float:
    return math.exp(-0.5 * sigma * sigma * (kx * kx + ky * ky))


def summarize(radius: float, width_x: float, width_y: float, sigma: float) -> None:
    angles = np.linspace(0, math.pi, 181)
    rows = []
    for theta in angles:
        kx = radius * math.cos(theta)
        ky = radius * math.sin(theta)
        rows.append((theta, box_response(kx, ky, width_x, width_y), gaussian_response(kx, ky, sigma)))

    box_vals = np.array([r[1] for r in rows])
    gauss_vals = np.array([r[2] for r in rows])
    print(f"|k|={radius:g}, box=({width_x:g},{width_y:g}), gaussian sigma={sigma:g}")
    print(f"  box min/max={box_vals.min():.6f}/{box_vals.max():.6f}; ratio={box_vals.max()/box_vals.min():.2f}")
    print(f"  gaussian min/max={gauss_vals.min():.6f}/{gauss_vals.max():.6f}; ratio={gauss_vals.max()/gauss_vals.min():.2f}")
    for deg in [0, 30, 45, 60, 90]:
        theta = math.radians(deg)
        kx = radius * math.cos(theta)
        ky = radius * math.sin(theta)
        print(
            f"    angle={deg:3d}: "
            f"box={box_response(kx, ky, width_x, width_y):.6f}, "
            f"gaussian={gaussian_response(kx, ky, sigma):.6f}"
        )
    print()


def main() -> None:
    print("DIRECTIONAL RESPONSE OF FINITE AVERAGING WINDOWS")
    print()
    summarize(radius=4.0, width_x=1.0, width_y=1.0, sigma=0.35)
    summarize(radius=4.0, width_x=1.0, width_y=2.0, sigma=0.35)


if __name__ == "__main__":
    main()
