"""TP5-TP8 hunt for the PF break order of K(x,y)=Phi(x-y), wide windows, dps 60."""
import json, random, sys, time
from multiprocessing import Pool
import mpmath as mp
sys.path.insert(0, "/root/precert")
import theta_common as tc

NPROC = 100
DPS = 60

def minor_task(args):
    order, seed, width = args
    mp.mp.dps = DPS
    rng = random.Random(seed)
    c = -3.0 + 6.0 * rng.random()
    xs = sorted(c + width * rng.random() for _ in range(order))
    c2 = -3.0 + 6.0 * rng.random()
    ys = sorted(c2 + width * rng.random() for _ in range(order))
    try:
        M = mp.matrix([[tc.phi_derivs(x - y, order=0)[0] for y in ys] for x in xs])
        d = mp.det(M)
        norm = mp.mpf(1)
        for i in range(order):
            norm *= max(abs(M[i, j]) for j in range(order))
        rel = d / norm if norm > 0 else mp.mpf(0)
        rl = tc.log10_or_none(rel)
        return {"order": order, "width": width, "xs": xs, "ys": ys,
                "rel_log10": rl, "sign": int(mp.sign(rel)),
                "resolved": bool(rl is not None and rl > -(DPS - 10))}
    except Exception as e:
        return {"order": order, "error": repr(e)}

def main():
    t0 = time.time()
    tasks = []; sd = 5 * 10**6
    for order in (5, 6, 7, 8):
        for width in (1.0, 2.0, 3.0, 4.5, 6.0):
            for _ in range(8000):
                tasks.append((order, sd, width)); sd += 1
    neg = {o: 0 for o in (5,6,7,8)}; negres = {o: 0 for o in (5,6,7,8)}
    tot = {o: 0 for o in (5,6,7,8)}
    examples = []
    with Pool(NPROC) as pool:
        for i, rec in enumerate(pool.imap_unordered(minor_task, tasks, chunksize=64)):
            if "error" in rec: continue
            o = rec["order"]; tot[o] += 1
            if rec["sign"] < 0:
                neg[o] += 1
                if rec["resolved"]:
                    negres[o] += 1
                    if negres[o] <= 3: examples.append(rec)
            if i % 40000 == 0:
                print(f"[{time.time()-t0:.0f}s] {i}/{len(tasks)} neg={neg} resolved_neg={negres}", flush=True)
    out = {"neg": neg, "resolved_neg": negres, "tot": tot, "examples": examples}
    json.dump(out, open("/root/precert/tp2_summary.json", "w"), indent=1)
    print("DONE", time.time()-t0); print(json.dumps(out)[:1500])

if __name__ == "__main__":
    main()
