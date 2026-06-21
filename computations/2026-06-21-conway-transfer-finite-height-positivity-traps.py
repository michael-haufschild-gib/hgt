#!/usr/bin/env python3
"""
Attempt 4 transfer experiment.

ResearchNode: positivity apex / no-margin uniform positivity.
NODE constraint: finite-window time averages need not equal ensemble averages.

Transfer:
  Replace time by height t and the trajectory observable by a continuum
  positivity observable P_a(t).  A localized sign-changing no-margin trap can
  leave broad finite-height averages positive while pointwise/all-scale
  positivity fails.
"""

from __future__ import annotations

import numpy as np


def curvature_window(a: float, x: np.ndarray) -> np.ndarray:
    """Scale-matched sign-changing profile: positive near 0, negative outside |x|>a."""
    return 2.0 * (a * a - x * x) / ((a * a + x * x) ** 2)


BASELINE = 0.035


def positivity_observable(t: np.ndarray, a: float, centers: list[float], amp: float) -> np.ndarray:
    # Positive baseline with localized sign-changing defects.
    y = np.ones_like(t) * BASELINE
    for c in centers:
        y += amp * curvature_window(a, t - c)
    return y


def window_means(t: np.ndarray, y: np.ndarray, width: float, stride: float) -> list[tuple[float, float, float]]:
    out: list[tuple[float, float, float]] = []
    start = float(t[0])
    stop = float(t[-1] - width)
    x = start
    while x <= stop:
        mask = (t >= x) & (t <= x + width)
        out.append((x, float(np.mean(y[mask])), float(np.min(y[mask]))))
        x += stride
    return out


def summarize(a: float, amp: float, centers: list[float], global_width: float) -> None:
    t = np.linspace(0.0, global_width, 20001)
    y = positivity_observable(t, a=a, centers=centers, amp=amp)
    global_mean = float(np.mean(y))
    global_min = float(np.min(y))
    print(f"a={a:g}, amp={amp:g}, centers={centers}")
    print(f"  global mean={global_mean:+.6e}, global min={global_min:+.6e}")
    for width in [2 * a, 10 * a, 50 * a, 200 * a]:
        wm = window_means(t, y, width=width, stride=width / 2)
        means = np.array([m for _, m, _ in wm])
        mins = np.array([mn for _, _, mn in wm])
        print(
            f"  window={width:7.2f}: "
            f"P(mean>0)={np.mean(means > 0):.3f}, "
            f"P(min<0)={np.mean(mins < 0):.3f}, "
            f"worst_mean={np.min(means):+.3e}, worst_min={np.min(mins):+.3e}"
        )
    print()


def main() -> None:
    print("FINITE-HEIGHT AVERAGES VS ALL-SCALE POSITIVITY")
    print("observable is continuum in height t and scale a; no zeta(n) values are used")
    print()
    a = 0.8
    probe = np.linspace(-8 * a, 8 * a, 20001)
    min_profile = float(np.min(curvature_window(a, probe)))
    critical_amp = BASELINE / abs(min_profile)
    print(f"sampled pointwise-failure boundary amp≈{critical_amp:.6f}")
    print()
    for factor in [0.8, 1.0, 1.2]:
        summarize(a=a, amp=factor * critical_amp, centers=[37.0], global_width=200.0)
    summarize(a=a, amp=1.2 * critical_amp, centers=[37.0, 117.0], global_width=200.0)


if __name__ == "__main__":
    main()
