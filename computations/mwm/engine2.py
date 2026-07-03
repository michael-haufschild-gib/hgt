#!/usr/bin/env python3.13
"""MWM winding engine v2 — parallel batched sweeps (campaign R2b/R3).

Optimizations vs engine.py: multiprocessing over boxes (30 workers on the 32-core pod),
sweep precision dps 18 (winding is an integer certificate — full 30 dps reserved for zero
certification), coarser initial contour (adaptive refinement handles the rest).
Only defects and progress lines are printed.

Usage:
  engine2.py sweep T1 T2 [H] [SIGMA1] [SIGMA2] [WORKERS] [DPS]
  engine2.py pencil C1 C2 STEPS T1 T2 [H]     # winding map for g_c = c*L(chi)+(1-c)*L(chibar)
"""
import sys, json
from multiprocessing import Pool
from mpmath import mp, mpc, mpf, pi, zeta, arg, sqrt, power, fabs

CHI = {1: mpc(1, 0), 2: mpc(0, 1), 3: mpc(0, -1), 4: mpc(-1, 0)}

def kappa():
    return (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)

def L_chi(s, conjugate=False):
    tot = mpc(0)
    for a in (1, 2, 3, 4):
        c = CHI[a].conjugate() if conjugate else CHI[a]
        tot += c * zeta(s, mpf(a) / 5)
    return power(5, -s) * tot

def f_dh(s):
    k = kappa()
    return (1 - 1j * k) / 2 * L_chi(s) + (1 + 1j * k) / 2 * L_chi(s, True)

_K = None  # pencil parameter: f_k = (1-ik)/2 L(chi) + (1+ik)/2 L(chibar); k = kappa is D-H (FE holds)

def f_pencil(s):
    return (1 - 1j * _K) / 2 * L_chi(s) + (1 + 1j * _K) / 2 * L_chi(s, True)

class ContourZero(Exception):
    pass

def _dphi(f, p0, v0, p1, v1, depth, stats):
    if fabs(v0) < mpf(10) ** (-mp.dps + 4) or fabs(v1) < mpf(10) ** (-mp.dps + 4):
        raise ContourZero
    d = arg(v1 / v0)
    if fabs(d) < mp.pi / 2:
        return d
    if depth <= 0:
        stats["unresolved"] += 1
        return d
    pm = (p0 + p1) / 2
    vm = f(pm)
    stats["evals"] += 1
    return _dphi(f, p0, v0, pm, vm, depth - 1, stats) + _dphi(f, pm, vm, p1, v1, depth - 1, stats)

def winding(f, s1, s2, t1, t2, per_edge=12, max_depth=18, nudge=mpf("1e-3"), tries=3):
    for _ in range(tries):
        stats = {"evals": 0, "unresolved": 0}
        corners = [mpc(s1, t1), mpc(s2, t1), mpc(s2, t2), mpc(s1, t2), mpc(s1, t1)]
        try:
            total = mpf(0)
            for c0, c1 in zip(corners, corners[1:]):
                pts = [c0 + (c1 - c0) * mpf(i) / per_edge for i in range(per_edge + 1)]
                vals = [f(p) for p in pts]
                stats["evals"] += len(vals)
                for i in range(per_edge):
                    total += _dphi(f, pts[i], vals[i], pts[i + 1], vals[i + 1], max_depth, stats)
            w = total / (2 * mp.pi)
            wr = int(mp.nint(w))
            ok = fabs(w - wr) < mpf("1e-5") and stats["unresolved"] == 0
            return {"w": wr, "raw": float(w), "ok": bool(ok), **stats,
                    "box": [float(s1), float(s2), float(t1), float(t2)]}
        except ContourZero:
            t1, t2 = t1 + nudge, t2 + nudge
            continue
    return {"w": None, "ok": False, "reason": "contour-zero",
            "box": [float(s1), float(s2), float(t1), float(t2)]}

def _init(dps, kval):
    global _K
    mp.dps = dps
    _K = mpf(kval)

def _box_dh(args):
    T, H, s1, s2 = args
    return winding(f_dh, s1, s2, T, T + H)

def _box_pencil(args):
    T, H, s1, s2 = args
    return winding(f_pencil, s1, s2, T, T + H)

def run_sweep(t1, t2, H, s1, s2, workers, dps):
    boxes = []
    T = mpf(t1)
    while T < mpf(t2):
        boxes.append((T, mpf(H), mpf(s1), mpf(s2)))
        T += mpf(H)
    ndef = 0
    with Pool(workers, initializer=_init, initargs=(dps, "0.28407904384041226899")) as pool:
        for res in pool.imap(_box_dh, boxes, chunksize=4):
            if res.get("w") not in (0,) or not res.get("ok"):
                ndef += 1
                print(json.dumps({"DEFECT": True, **res}), flush=True)
    print(json.dumps({"done": [float(t1), float(t2)], "boxes": len(boxes),
                      "defects_or_flags": ndef}), flush=True)

def run_pencil(k1, k2, steps, t1, t2, H, s1="0.51", workers=30, dps=18):
    # walk k along [k1,k2] in f_k = (1-ik)/2 L + (1+ik)/2 Lbar; k=kappa ~ 0.2841 is D-H (FE)
    for j in range(steps + 1):
        kv = mpf(k1) + (mpf(k2) - mpf(k1)) * j / steps
        boxes = []
        T = mpf(t1)
        while T < mpf(t2):
            boxes.append((T, mpf(H), mpf(s1), mpf("1.2")))
            T += mpf(H)
        found = []
        with Pool(workers, initializer=_init, initargs=(dps, str(kv))) as pool:
            for res in pool.imap(_box_pencil, boxes, chunksize=2):
                if res.get("w") not in (0,) or not res.get("ok"):
                    found.append(res)
        print(json.dumps({"k": float(kv), "defects": found}), flush=True)

if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "sweep":
        a = sys.argv[2:]
        run_sweep(a[0], a[1],
                  a[2] if len(a) > 2 else 2,
                  a[3] if len(a) > 3 else "0.55",
                  a[4] if len(a) > 4 else "1.2",
                  int(a[5]) if len(a) > 5 else 30,
                  int(a[6]) if len(a) > 6 else 18)
    elif cmd == "pencil":
        a = sys.argv[2:]
        run_pencil(a[0], a[1], int(a[2]), a[3], a[4], a[5] if len(a) > 5 else 2,
                   a[6] if len(a) > 6 else "0.51")
    else:
        print(json.dumps({"error": "unknown", "cmd": cmd}))
        sys.exit(1)
