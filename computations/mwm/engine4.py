#!/usr/bin/env python3.13
"""MWM engine v4 — R6: boundary-data return measurement at a D-H defect box.

Tests the (H)-mechanism shape (07-index-formula.md par.3) in the family where defects
exist: fix a certified w=1 defect box B* of f_dh, measure the margin proxy
m = min |f| over a fixed boundary sample of dB*, and the return distance
d(tau) = max over the same sample of |f(s + i tau) - f(s)|, on a tau-grid.
Sub-margin returns (d < m) are Rouche-transfer candidates; certify each candidate
separately with the winding engine (engine2.winding) on the shifted box.
Sampled sup/min are proxies (both on the SAME point set, so internally consistent);
certification is by winding, never by the proxy.

Usage:
  engine4.py returns S1 S2 T1 T2 TAU1 TAU2 STEP [PER_EDGE] [WORKERS] [DPS]
"""
import sys, json
from multiprocessing import Pool
from mpmath import mp, mpc, mpf
from engine2 import f_dh

def boundary_points(s1, s2, t1, t2, per_edge):
    corners = [mpc(s1, t1), mpc(s2, t1), mpc(s2, t2), mpc(s1, t2), mpc(s1, t1)]
    pts = []
    for c0, c1 in zip(corners, corners[1:]):
        for i in range(per_edge):
            pts.append(c0 + (c1 - c0) * mpf(i) / per_edge)
    return pts

_PTS = None
_VALS = None

def _init(dps, s1, s2, t1, t2, per_edge):
    global _PTS, _VALS
    mp.dps = dps
    _PTS = boundary_points(mpf(s1), mpf(s2), mpf(t1), mpf(t2), per_edge)
    _VALS = [f_dh(p) for p in _PTS]

def _dist(tau):
    t = mpf(tau)
    d = mpf(0)
    for p, v in zip(_PTS, _VALS):
        dd = abs(f_dh(p + mpc(0, 1) * t) - v)
        if dd > d:
            d = dd
    return (float(tau), float(d))

def run_returns(s1, s2, t1, t2, tau1, tau2, step, per_edge, workers, dps):
    mp.dps = dps
    pts = boundary_points(mpf(s1), mpf(s2), mpf(t1), mpf(t2), per_edge)
    vals = [f_dh(p) for p in pts]
    margin = min(abs(v) for v in vals)
    print(json.dumps({"box": [float(mpf(s1)), float(mpf(s2)), float(mpf(t1)), float(mpf(t2))],
                      "per_edge": per_edge, "margin_proxy": float(margin)}), flush=True)
    taus = []
    tau = mpf(tau1)
    while tau <= mpf(tau2):
        taus.append(str(tau))
        tau += mpf(step)
    with Pool(workers, initializer=_init, initargs=(dps, s1, s2, t1, t2, per_edge)) as pool:
        for tau_f, d in pool.imap(_dist, taus, chunksize=16):
            print(json.dumps({"tau": tau_f, "d": d}), flush=True)

if __name__ == "__main__":
    if len(sys.argv) < 2 or sys.argv[1] != "returns":
        print(json.dumps({"error": "unknown", "argv": sys.argv[1:]}))
        sys.exit(1)
    a = sys.argv[2:]
    run_returns(a[0], a[1], a[2], a[3], a[4], a[5], a[6],
                int(a[7]) if len(a) > 7 else 30,
                int(a[8]) if len(a) > 8 else 30,
                int(a[9]) if len(a) > 9 else 15)
