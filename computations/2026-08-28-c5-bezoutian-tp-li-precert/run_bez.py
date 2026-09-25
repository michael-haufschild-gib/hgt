"""Experiment 2: Bezoutian rank ladder (GORZ red-flag test) + adversarial hunt.

RH  <=>  [B(w_j, conj w_k)]_{jk} PSD for every finite node system, Re w > 1/2
(Lean: riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian).

Draw random node systems per (rank, regime), compute relative margin
lambda_min / lambda_max, track margin decay vs rank, then run adversarial
local search from the worst draw of each rank to try to push the margin
negative (a confirmed negative at high precision would contradict RH).
"""

import json
import random
import sys
import time
from multiprocessing import Pool

import mpmath as mp

sys.path.insert(0, ".")
import theta_common as tc

NPROC = 80
RANKS = [2, 4, 6, 8, 10, 12, 16, 20]


def init():
    random.seed()


def draw_nodes(rank, regime, rng):
    nodes = []
    if regime == "moderate":
        for _ in range(rank):
            nodes.append(mp.mpc(0.501 + 2.0 * rng.random(),
                                -40 + 80 * rng.random()))
    elif regime == "clustered":
        c = mp.mpc(0.52 + 1.0 * rng.random(), -30 + 60 * rng.random())
        for _ in range(rank):
            z = c + mp.mpc(rng.gauss(0, 0.03), rng.gauss(0, 0.03))
            if mp.re(z) <= 0.5:
                z = mp.mpc(0.5 + abs(mp.re(z) - 0.5) + 1e-6, mp.im(z))
            nodes.append(z)
    elif regime == "tall":
        s = 1 if rng.random() < 0.5 else -1
        for _ in range(rank):
            nodes.append(mp.mpc(0.501 + 1.0 * rng.random(),
                                s * (150 + 200 * rng.random())))
    elif regime == "edge":
        for _ in range(rank):
            nodes.append(mp.mpc(0.5 + 1e-4 + 0.02 * rng.random(),
                                -60 + 120 * rng.random()))
    return nodes


def margin_of(nodes):
    M = tc.bezoutian_matrix(nodes)
    lo, hi, _ = tc.hermitian_min_max_eig(M)
    return lo / hi, lo, hi


def one_draw(args):
    rank, regime, seed, dps = args
    mp.mp.dps = dps
    rng = random.Random(seed)
    try:
        nodes = draw_nodes(rank, regime, rng)
        rel, lo, hi = margin_of(nodes)
        return {"rank": rank, "regime": regime, "seed": seed,
                "rel_log10": tc.log10_or_none(rel),
                "rel_sign": int(mp.sign(rel)),
                "lo_log10": tc.log10_or_none(lo), "lo_sign": int(mp.sign(lo)),
                "nodes": [[float(mp.re(z)), float(mp.im(z))] for z in nodes]}
    except Exception as e:
        return {"rank": rank, "regime": regime, "seed": seed, "error": repr(e)}


def adversarial(args):
    rank, nodes_ri, seed, dps, steps = args
    mp.mp.dps = dps
    rng = random.Random(seed)
    nodes = [mp.mpc(a, b) for a, b in nodes_ri]
    rel, lo, hi = margin_of(nodes)
    best = rel
    sigma = 0.05
    hist = [tc.log10_or_none(best)]
    for i in range(steps):
        cand = []
        for z in nodes:
            z2 = z + mp.mpc(rng.gauss(0, sigma), rng.gauss(0, sigma * 5))
            if mp.re(z2) <= 0.5:
                z2 = mp.mpc(0.5 + 1e-6 + abs(mp.re(z2) - 0.5) * 0.1, mp.im(z2))
            cand.append(z2)
        try:
            rel2, lo2, _ = margin_of(cand)
        except Exception:
            continue
        if rel2 < best:
            best = rel2
            nodes = cand
            sigma = min(sigma * 1.3, 0.3)
        else:
            sigma = max(sigma * 0.93, 1e-4)
        if i % 40 == 0:
            hist.append(tc.log10_or_none(best))
    return {"rank": rank, "final_rel_log10": tc.log10_or_none(best),
            "final_sign": int(mp.sign(best)),
            "nodes": [[float(mp.re(z)), float(mp.im(z))] for z in nodes],
            "history": hist}


def main():
    t0 = time.time()
    tasks = []
    sd = 1
    for rank in RANKS:
        for regime, ndraw, dps in (("moderate", 150, 60), ("clustered", 150, 80),
                                   ("edge", 150, 60), ("tall", 40, 80)):
            for _ in range(ndraw):
                tasks.append((rank, regime, sd, dps))
                sd += 1
    out = open("bez_draws.jsonl", "w")
    worst_by_rank = {}
    with Pool(NPROC, initializer=init) as pool:
        for i, rec in enumerate(pool.imap_unordered(one_draw, tasks, chunksize=4)):
            out.write(json.dumps(rec) + "\n")
            if "error" in rec:
                continue
            r = rec["rank"]
            if rec["rel_sign"] < 0:
                print("NEGATIVE MARGIN DRAW:", json.dumps(rec), flush=True)
            if r not in worst_by_rank or (rec["rel_log10"] or -1e9) < (worst_by_rank[r]["rel_log10"] or -1e9):
                if rec["rel_sign"] > 0:
                    worst_by_rank[r] = rec
            if i % 200 == 0:
                print(f"[{time.time()-t0:.0f}s] draws {i}/{len(tasks)}", flush=True)
    out.close()
    print("draws done", time.time() - t0)

    adv_tasks = []
    for rank, rec in sorted(worst_by_rank.items()):
        adv_tasks.append((rank, rec["nodes"], 777 + rank, 80, 250))
    results = []
    with Pool(min(NPROC, len(adv_tasks)), initializer=init) as pool:
        for rec in pool.imap_unordered(adversarial, adv_tasks):
            results.append(rec)
            print("ADV:", json.dumps({k: rec[k] for k in ("rank", "final_rel_log10", "final_sign")}), flush=True)
    with open("bez_summary.json", "w") as f:
        json.dump({"worst_by_rank": worst_by_rank, "adversarial": results}, f, indent=1)
    print("DONE", time.time() - t0)


if __name__ == "__main__":
    main()
