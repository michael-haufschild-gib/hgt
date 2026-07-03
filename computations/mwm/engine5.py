#!/usr/bin/env python3.13
"""MWM engine v5 — R6-loc: LOCAL return measurement on a small circle around a D-H zero.

Circle C = s0 + r·e^{2πik/N}, N sample points. margin = min |f| on C (sampled proxy).
d(tau) = max over C of |f(s + i·tau) − f(s)|. A sub-margin return transfers the enclosed
zero configuration by Rouché (07-index-formula.md §3), now at the LOCAL scale: the circle
data is dominated by finitely many Taylor coefficients, so returns are a finite-dimensional
value-recurrence event — the (H-loc) probe contrasting R6's big-box negative.

Usage:
  engine5.py circle S0RE S0IM R NPTS TAU1 TAU2 STEP [WORKERS] [DPS]
"""
import sys, json
from multiprocessing import Pool
from mpmath import mp, mpc, mpf, expjpi
from engine2 import f_dh

_PTS = None
_VALS = None

def circle_points(s0re, s0im, r, npts):
    s0 = mpc(mpf(s0re), mpf(s0im))
    rr = mpf(r)
    return [s0 + rr * expjpi(mpf(2 * k) / npts) for k in range(npts)]

def _init(dps, s0re, s0im, r, npts):
    global _PTS, _VALS
    mp.dps = dps
    _PTS = circle_points(s0re, s0im, r, npts)
    _VALS = [f_dh(p) for p in _PTS]

def _dist(tau):
    t = mpf(tau)
    d = mpf(0)
    for p, v in zip(_PTS, _VALS):
        dd = abs(f_dh(p + mpc(0, 1) * t) - v)
        if dd > d:
            d = dd
    return (float(tau), float(d))

def run_circle(s0re, s0im, r, npts, tau1, tau2, step, workers, dps):
    mp.dps = dps
    pts = circle_points(s0re, s0im, r, npts)
    vals = [f_dh(p) for p in pts]
    margin = min(abs(v) for v in vals)
    print(json.dumps({"s0": [float(mpf(s0re)), float(mpf(s0im))], "r": float(mpf(r)),
                      "npts": npts, "margin_proxy": float(margin)}), flush=True)
    taus = []
    tau = mpf(tau1)
    while tau <= mpf(tau2):
        taus.append(str(tau))
        tau += mpf(step)
    with Pool(workers, initializer=_init, initargs=(dps, s0re, s0im, r, npts)) as pool:
        for tf, d in pool.imap(_dist, taus, chunksize=16):
            print(json.dumps({"tau": tf, "d": d}), flush=True)

if __name__ == "__main__":
    if len(sys.argv) < 2 or sys.argv[1] != "circle":
        print(json.dumps({"error": "unknown", "argv": sys.argv[1:]}))
        sys.exit(1)
    a = sys.argv[2:]
    run_circle(a[0], a[1], a[2], int(a[3]), a[4], a[5], a[6],
               int(a[7]) if len(a) > 7 else 30,
               int(a[8]) if len(a) > 8 else 15)
