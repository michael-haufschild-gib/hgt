#!/usr/bin/env python3
import math

import mpmath as mp
import numpy as np


def gamma_part(s):
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def phase_defect(g, p):
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def component(kind, s):
    if kind == "true-zeta":
        return dlog_zeta(s)
    if kind == "sine-control":
        return 0.9 * gamma_part(s) * complex(math.cos(0.37 * s.imag), math.sin(0.37 * s.imag))
    if kind == "antiphase-sine":
        return -0.9 * gamma_part(s) * complex(math.cos(0.37 * s.imag), math.sin(0.37 * s.imag))
    raise ValueError(kind)


def summarize(kind, sigma, window):
    shifts = []
    defects = []
    for t in np.linspace(window[0], window[1], 220):
        s = complex(sigma, float(t))
        g = gamma_part(s)
        p = component(kind, s)
        ideal = math.log((abs(p) + 1e-12) / (abs(g) + 1e-12))
        active = math.log((abs(g + p) + 1e-12) / (abs(g) + 1e-12))
        shifts.append(active - ideal)
        defects.append(phase_defect(g, p))
    return float(np.median(shifts)), float(np.median(defects)), float(np.mean(np.array(shifts) < -0.5))


def main():
    print("STEP11 redox activity similar-object controls")
    print("method=8 look-for-similar-objects; smooth sine and antiphase controls")
    print("kind sigma window shift_med defect_med frac_shift_lt_-0.5")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5]:
            for kind in ["true-zeta", "sine-control", "antiphase-sine"]:
                s, d, f = summarize(kind, sigma, window)
                print(f"{kind:14s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {s:.6f} {d:.6f} {f:.6f}")


if __name__ == "__main__":
    main()
