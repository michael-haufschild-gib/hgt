#!/usr/bin/env python3.13
"""MWM winding engine v3 — complex-c pencil path (campaign R5: Euler-approach profile).

Walks c along the straight segment from the D-H point c_DH = (1 - i*kappa)/2 (FE holds,
off-line zeros exist) to c = 1 (pure L(s,chi): Euler product) inside
f_c = c*L(chi) + (1-c)*L(chibar), and reports off-line winding defects per step.
Pre-registered observable (05-task-board.md R5): defect count along u in [0,1]; the SHAPE
near c = 1 (linear vanishing vs threshold); any defect surviving near c = 1 is an anomaly.

Usage:
  engine3.py cpath U1 U2 STEPS T1 T2 [H] [SIGMA1] [WORKERS] [DPS]
"""
import sys, json
from multiprocessing import Pool
from mpmath import mp, mpc, mpf
from engine2 import L_chi, kappa, winding

_C = None  # path parameter: c(u) = (1-u)*c_DH + u, u=0 is D-H (FE), u=1 is pure L(chi)

def f_cpath(s):
    return _C * L_chi(s) + (1 - _C) * L_chi(s, True)

def _init(dps, cre, cim):
    global _C
    mp.dps = dps
    _C = mpc(mpf(cre), mpf(cim))

def _box(args):
    T, H, s1, s2 = args
    return winding(f_cpath, s1, s2, T, T + H)

def run_cpath(u1, u2, steps, t1, t2, H, s1, workers, dps):
    mp.dps = max(dps + 12, 30)  # parent computes c to full precision before handing to workers
    c_dh = mpc(1, 0) / 2 * (1 - mpc(0, 1) * kappa())
    for j in range(steps + 1):
        u = mpf(u1) + (mpf(u2) - mpf(u1)) * j / steps
        c = (1 - u) * c_dh + u
        boxes = []
        T = mpf(t1)
        while T < mpf(t2):
            boxes.append((T, mpf(H), mpf(s1), mpf("1.2")))
            T += mpf(H)
        found = []
        with Pool(workers, initializer=_init,
                  initargs=(dps, mp.nstr(c.real, 25), mp.nstr(c.imag, 25))) as pool:
            for res in pool.imap(_box, boxes, chunksize=2):
                if res.get("w") not in (0,) or not res.get("ok"):
                    found.append(res)
        print(json.dumps({"u": float(u), "c": [float(c.real), float(c.imag)],
                          "n_defects": len(found), "defects": found}), flush=True)

if __name__ == "__main__":
    if len(sys.argv) < 2 or sys.argv[1] != "cpath":
        print(json.dumps({"error": "unknown", "argv": sys.argv[1:]}))
        sys.exit(1)
    a = sys.argv[2:]
    run_cpath(a[0], a[1], int(a[2]), a[3], a[4],
              a[5] if len(a) > 5 else 2,
              a[6] if len(a) > 6 else "0.51",
              int(a[7]) if len(a) > 7 else 30,
              int(a[8]) if len(a) > 8 else 18)
