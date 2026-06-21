#!/usr/bin/env python3
"""
Attempt 10 transfer experiment.

ResearchNode: affine confinement.
NODE constraint: Gauss-Newton/Fisher keeps a PSD part and drops residual
curvature, missing negative saddle curvature.

Transfer:
  Model an affine-confined positive approximation as a retained PSD baseline,
  and the seam/off-line-pair stress as the signed residual curvature profile
      C_a(t)=2(a^2-t^2)/(a^2+t^2)^2.
  The retained part is positive everywhere; sign change is carried only by the
  dropped residual/transverse term.
"""

from __future__ import annotations

import numpy as np


def seam_curvature(a: float, t: np.ndarray) -> np.ndarray:
    return 2.0 * (a * a - t * t) / ((a * a + t * t) ** 2)


def summarize(a: float, baseline: float, amp: float) -> None:
    t = np.linspace(-5 * a, 5 * a, 20001)
    retained = np.full_like(t, baseline)
    residual = amp * seam_curvature(a, t)
    full = retained + residual
    print(f"a={a:g}, baseline={baseline:g}, amp={amp:g}")
    print(f"  retained min={retained.min():+.6e}; negative_count={np.sum(retained < 0)}")
    print(f"  residual min/max={residual.min():+.6e}/{residual.max():+.6e}")
    print(f"  full min={full.min():+.6e}; negative_count={np.sum(full < 0)}")
    idx = int(np.argmin(full))
    print(f"  worst t={t[idx]:+.6f}, retained={retained[idx]:+.6e}, residual={residual[idx]:+.6e}")
    print()


def main() -> None:
    print("AFFINE/GAUSS-NEWTON POSITIVE PART VS SEAM CURVATURE")
    print("retained PSD part alone cannot see the signed residual curvature")
    print()
    summarize(a=0.5, baseline=0.2, amp=0.02)
    summarize(a=0.5, baseline=0.2, amp=0.08)
    summarize(a=0.2, baseline=0.2, amp=0.02)
    summarize(a=0.2, baseline=0.2, amp=0.04)


if __name__ == "__main__":
    main()
