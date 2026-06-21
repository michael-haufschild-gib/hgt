#!/usr/bin/env python3
"""
R36 STEP 11: reverse the downstream-filter statement.

Question: if broad positive filters erase the off-line curvature core, does a
matched sign-changing filter recover it, and does that filter avoid false
positives on a purely on-line negative curvature background?
"""

from __future__ import annotations

import numpy as np


def quartet_curvature(tau: np.ndarray, a: float) -> np.ndarray:
    return 2.0 * (a * a - tau * tau) / ((a * a + tau * tau) ** 2)


def online_negative(tau: np.ndarray, a: float) -> np.ndarray:
    return -2.0 * a * a / ((a * a + tau * tau) ** 2)


def lowpass_kernel(x: np.ndarray, width: float) -> np.ndarray:
    k = np.exp(-0.5 * (x / width) ** 2)
    return k / k.sum()


def matched_kernel(x: np.ndarray, a: float) -> np.ndarray:
    k = quartet_curvature(x, a)
    k = k - k.mean()
    norm = np.sqrt(np.sum(k * k))
    return k / (norm + 1e-12)


def response(y: np.ndarray, k: np.ndarray) -> float:
    z = np.convolve(y, k[::-1], mode="same")
    return float(z[len(z) // 2])


def main() -> None:
    print("a      lowpass_offline  matched_offline  lowpass_online  matched_online")
    for a in [0.05, 0.08, 0.12, 0.20]:
        t = np.linspace(-20 * a, 20 * a, 8001)
        x = np.linspace(-8 * a, 8 * a, 1601)
        off = quartet_curvature(t, a)
        on = online_negative(t, a)
        lp = lowpass_kernel(x, 6 * a)
        mh = matched_kernel(x, a)
        print(
            f"{a:4.2f} {response(off, lp):15.6f} {response(off, mh):16.6f} "
            f"{response(on, lp):14.6f} {response(on, mh):15.6f}"
        )
    print("\nInterpretation")
    print(
        "The reverse test separates filters at the localized center: positive low-pass "
        "readouts erase localization, while the sign-changing matched filter recovers "
        "the off-line core without turning the purely negative on-line center positive."
    )


if __name__ == "__main__":
    main()
