"""Experiment 3: total-positivity order of the translation kernel K(x,y)=Phi(x-y).

TP2 is the proved log-concavity. The master-mechanism question is whether a
HIGHER TP order holds (it would power an all-rank Hankel mechanism), or fails
(then the C5 mechanism must be weaker than kernel total positivity).
Tests random ordered 3x3 and 4x4 minors det[Phi(x_i - y_j)].
"""

import json
import random
import sys
import time
from multiprocessing import Pool

import mpmath as mp

sys.path.insert(0, ".")
import theta_common as tc

NPROC = 40
DPS = 40


def minor_task(args):
    order, seed, width = args
    mp.mp.dps = DPS
    rng = random.Random(seed)
    c = -2.0 + 4.0 * rng.random()
    xs = sorted(c + width * rng.random() for _ in range(order))
    c2 = -2.0 + 4.0 * rng.random()
    ys = sorted(c2 + width * rng.random() for _ in range(order))
    try:
        rows = []
        for x in xs:
            row = []
            for y in ys:
                row.append(tc.phi_derivs(x - y, order=0)[0])
            rows.append(row)
        M = mp.matrix(rows)
        d = mp.det(M)
        norm = mp.mpf(1)
        for i in range(order):
            norm *= max(abs(M[i, j]) for j in range(order))
        rel = d / norm if norm > 0 else mp.mpf(0)
        return {"order": order, "width": width, "xs": xs, "ys": ys,
                "rel_log10": tc.log10_or_none(rel), "sign": int(mp.sign(rel))}
    except Exception as e:
        return {"order": order, "error": repr(e)}


def main():
    t0 = time.time()
    tasks = []
    sd = 10 ** 6
    for order in (2, 3, 4):
        for width in (0.5, 1.0, 2.0, 3.0):
            n = 30000 if order == 2 else 25000
            for _ in range(n):
                tasks.append((order, sd, width))
                sd += 1
    neg = {2: 0, 3: 0, 4: 0}
    tot = {2: 0, 3: 0, 4: 0}
    worst = {}
    examples = []
    with Pool(NPROC) as pool:
        for i, rec in enumerate(pool.imap_unordered(minor_task, tasks, chunksize=256)):
            if "error" in rec:
                continue
            o = rec["order"]
            tot[o] += 1
            if rec["sign"] < 0:
                neg[o] += 1
                if neg[o] <= 5:
                    examples.append(rec)
            key = o
            if rec["sign"] > 0 and (key not in worst or (rec["rel_log10"] or 0) < (worst[key]["rel_log10"] or 0)):
                worst[key] = {"rel_log10": rec["rel_log10"], "width": rec["width"]}
            if i % 50000 == 0:
                print(f"[{time.time()-t0:.0f}s] {i}/{len(tasks)} neg={neg}", flush=True)
    summary = {"negatives": neg, "totals": tot,
               "worst_positive_rel_log10": worst, "first_negative_examples": examples}
    with open("tp_summary.json", "w") as f:
        json.dump(summary, f, indent=1)
    print("DONE", time.time() - t0)
    print(json.dumps(summary)[:2000])


if __name__ == "__main__":
    main()
