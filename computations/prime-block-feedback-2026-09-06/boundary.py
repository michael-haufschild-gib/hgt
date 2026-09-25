"""Run on the authorized pod. Finite empirical bridge, never a Lean input."""
import argparse
import json
import multiprocessing as mp
import time
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss

ROOT = Path(__file__).resolve().parent
PRIMES = None
RANGES = None


def reference(a, b, n):
    z, w = leggauss(n)
    mid = (a+b)/2
    radius = (b-a)/2
    x = mid[:,None] + radius[:,None]*z[None,:]
    return radius*np.sum(w[None,:]/np.log(x), axis=1)


def phase_job(t):
    results, raw = [], []
    for low, high in RANGES:
        kvals = np.arange(low, high, dtype=np.int64)
        widths = (kvals+1)**4-kvals**4
        edges = kvals[:,None]**4 + (widths[:,None]*(8*np.arange(17)[None,:]+t))//128
        assert edges.max() < (high+1)**4
        a, b = edges[:,:-1].ravel(), edges[:,1:].ravel()
        counts = np.searchsorted(PRIMES,b)-np.searchsorted(PRIMES,a)
        mass = reference(a,b,32)
        refined = reference(a,b,64)
        qerror = float(np.max(np.abs(refined-mass)/mass))
        assert qerror < 1e-12
        c = counts-mass
        fine = c/np.sqrt(mass)
        whole = c.reshape(-1,16).sum(axis=1)/np.sqrt(mass.reshape(-1,16).sum(axis=1))
        fine_mse, whole_mse = float(np.mean(fine*fine)), float(np.mean(whole*whole))
        child_mse = (fine*fine).reshape(-1,16).mean(axis=1)
        results.append({"range": [int(low),int(high-1)],
            "fine_mean_square": fine_mse, "whole_mean_square": whole_mse,
            "ratio": whole_mse/fine_mse, "max_whole_absolute": float(np.max(np.abs(whole))),
            "individually_expanding_blocks": int(np.sum(whole*whole > child_mse)),
            "quadrature_relative_error": qerror})
        raw.append(np.column_stack([np.full(len(a),t),np.repeat(kvals,16),
            np.tile(np.arange(16),len(kvals)),a,b,counts,mass]))
    return {"phase_eighths":t,"ranges":results}, np.concatenate(raw)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=["discovery","validation"])
    args = parser.parse_args()
    start = time.monotonic()
    PRIMES = np.load(ROOT/"primes.npy",mmap_mode="r")
    if args.phase == "discovery":
        PRIMES = PRIMES[:np.searchsorted(PRIMES,32**4)]
        RANGES = [(4,23),(24,31)]
    else:
        gate = json.loads((ROOT/"boundary-discovery.json").read_text())
        assert gate["advance"], "Held-out ranges require a passed discovery gate."
        RANGES = [(32,63),(64,89)]
    with mp.get_context("fork").Pool(8) as pool:
        entries = pool.map(phase_job,range(8))
    results = [entry[0] for entry in entries]
    np.savez_compressed(ROOT/f"boundary-{args.phase}-rows.npz",
                        rows=np.concatenate([entry[1] for entry in entries]))
    out = {"candidate":"[BRIDGE] B2","phase":args.phase,"results":results,
        "advance":all(r["ratio"] <= .5 for entry in results for r in entry["ranges"]),
        "wall_seconds":time.monotonic()-start}
    (ROOT/f"boundary-{args.phase}.json").write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))
