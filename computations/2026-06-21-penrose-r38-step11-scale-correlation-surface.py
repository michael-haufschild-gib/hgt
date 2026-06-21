#!/usr/bin/env python3
"""
R38 STEP 11: change representation to a two-scale correlation surface.
"""

from __future__ import annotations

import numpy as np


def quartet_curvature(tau: np.ndarray, a: float) -> np.ndarray:
    return 2.0 * (a * a - tau * tau) / ((a * a + tau * tau) ** 2)


def gaussian_filter(y: np.ndarray, dt: float, width: float) -> np.ndarray:
    radius = min(len(y) // 2 - 1, max(6, int(6 * width / dt)))
    x = np.arange(-radius, radius + 1) * dt
    k = np.exp(-0.5 * (x / width) ** 2)
    k /= k.sum()
    return np.convolve(y, k, mode="same")


def corr(x: np.ndarray, y: np.ndarray) -> float:
    x = x - x.mean()
    y = y - y.mean()
    return float(np.dot(x, y) / ((np.linalg.norm(x) * np.linalg.norm(y)) + 1e-12))


def main() -> None:
    a = 0.10
    t = np.linspace(-12 * a, 12 * a, 6001)
    dt = t[1] - t[0]
    route_a = quartet_curvature(t, a)
    route_b = np.exp(-0.5 * (t / (0.42 * a)) ** 2) - 0.12 * np.exp(-0.5 * (t / (1.5 * a)) ** 2)
    widths = [0.12, 0.18, 0.25, 0.35, 0.50, 0.75, 1.00, 1.50, 2.00, 3.00]
    best = (-1.0, None, None)
    print("correlation surface rows=routeA width/a, cols=routeB width/a")
    print("      " + " ".join(f"{w:5.2f}" for w in widths))
    for wa in widths:
        fa = gaussian_filter(route_a, dt, wa * a)
        vals = []
        for wb in widths:
            fb = gaussian_filter(route_b, dt, wb * a)
            c = corr(fa, fb)
            vals.append(c)
            if c > best[0]:
                best = (c, wa, wb)
        print(f"{wa:5.2f} " + " ".join(f"{v:5.2f}" for v in vals))
    print(f"\nbest_corr={best[0]:.6f} at widthA/a={best[1]:.2f}, widthB/a={best[2]:.2f}")
    print(
        "Interpretation: changing representation from one fixed filter pair to a scale-correlation "
        "surface reveals a high-correlation ridge. The G-C15 test should compare entrances after "
        "joint scale alignment, not after independent preprocessing."
    )


if __name__ == "__main__":
    main()
