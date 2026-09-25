"""Experiment 1: global grid certification of C5(u,t) >= 0 (CLG/TTF rank-four gate).

Computes the dimensionless margins  C5/P^2 (action form)  and  C5/A^2
(= logistic barrier defect  y(10+y) - 5 t y')  on a dense (u,t) grid,
records the minimum manifold, and cross-checks the two exact Lean identities
C5 = P^2 * action  and  C5 = A^2 * barrier at every point.
"""

import json
import sys
import time
from multiprocessing import Pool

import mpmath as mp

sys.path.insert(0, ".")
import theta_common as tc

DPS = 40
NPROC = 120


def init():
    mp.mp.dps = DPS


def eval_point(args):
    u, t = args
    try:
        d = tc.c5_point(u, t)
        return {
            "u": float(u), "t": float(t),
            "c5P2": tc.log10_or_none(d["c5_over_P2"]),
            "c5P2_sign": int(mp.sign(d["c5_over_P2"])),
            "c5A2": float(d["c5_over_A2"]),
            "y": float(d["y"]),
            "r_log10": tc.log10_or_none(d["r"]),
            "tq1": float(d["tq1"]) if abs(d["tq1"]) < 1e300 else None,
            "t2q2": float(d["t2q2"]) if abs(d["t2q2"]) < 1e300 else None,
            "chkA": tc.log10_or_none(d["chk_action"]),
            "chkB": tc.log10_or_none(d["chk_barrier"]),
            "c5A2_str": mp.nstr(d["c5_over_A2"], 12),
        }
    except Exception as e:
        return {"u": float(u), "t": float(t), "error": repr(e)}


def main():
    us = [mp.mpf(i) / 20 for i in range(0, 121)]           # u in [0, 6] step 0.05
    # t grid: geometric 1e-3 .. 8, 480 points
    ts = [mp.mpf(10) ** (mp.mpf(-3) + mp.mpf(i) * (mp.log10(mp.mpf(8)) + 3) / 479)
          for i in range(480)]
    tasks = [(float(u), float(t)) for u in us for t in ts]
    # evenness spot checks: a few negative u
    tasks += [(-1.0, 0.7), (-2.5, 1.3), (-0.35, 2.2)]
    t0 = time.time()
    out = open("c5_grid.jsonl", "w")
    worst = None
    nbad = 0
    with Pool(NPROC, initializer=init) as pool:
        for i, rec in enumerate(pool.imap_unordered(eval_point, tasks, chunksize=64)):
            out.write(json.dumps(rec) + "\n")
            if "error" in rec:
                nbad += 1
                continue
            if worst is None or rec["c5A2"] < worst["c5A2"]:
                worst = rec
            if i % 5000 == 0:
                print(f"[{time.time()-t0:.0f}s] {i}/{len(tasks)} worst so far:",
                      None if worst is None else (worst["u"], worst["t"], worst["c5A2"]),
                      flush=True)
    out.close()
    print("DONE grid", time.time() - t0, "s; errors:", nbad)
    print("WORST:", json.dumps(worst))

    # refinement around the worst point
    if worst is not None:
        u0, t0_ = worst["u"], worst["t"]
        fine = []
        for du in range(-20, 21):
            for dt in range(-20, 21):
                uu = u0 + du * 0.005
                tt = t0_ * (1 + dt * 0.004)
                if tt > 0:
                    fine.append((uu, tt))
        best = None
        with Pool(NPROC, initializer=init) as pool:
            for rec in pool.imap_unordered(eval_point, fine, chunksize=32):
                if "error" not in rec and (best is None or rec["c5A2"] < best["c5A2"]):
                    best = rec
        print("REFINED WORST:", json.dumps(best))
        with open("c5_summary.json", "w") as f:
            json.dump({"grid_worst": worst, "refined_worst": best,
                       "n_tasks": len(tasks), "errors": nbad}, f, indent=1)


if __name__ == "__main__":
    main()
