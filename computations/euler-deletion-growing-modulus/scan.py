"""Runpod-only exploration of literal mixed sums; not proof certificates."""
import os
for name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"

import concurrent.futures
import json
import math
import platform
import time
import mpmath as mp
import numpy as np

MODULI = tuple(2 ** j for j in range(4, 14))
CELL_CUTOFFS = (128, 512, 2048)
CHUNK = 262144

def packed(z):
    return [float(z.real), float(z.imag)]

def task(spec):
    started = time.time()
    mp.mp.dps = 65
    height = mp.im(mp.zetazero(spec["zero"])) if "zero" in spec else mp.mpf(spec["t"])
    sm = mp.mpc(spec["sigma"], height)
    s = complex(sm)
    z = complex(mp.zeta(sm))
    alpha = 2 - 2 * s.real
    constant = complex(mp.zeta(2 * mp.re(sm) - 1) / (1 - mp.conj(sm)))
    nmax = MODULI[-1] * CELL_CUTOFFS[-1]
    prefixes = np.empty(nmax + 1, dtype=np.complex128)
    prefixes[0] = 0
    for start in range(0, nmax, CHUNK):
        stop = min(start + CHUNK, nmax)
        ns = np.arange(start + 1, stop + 1, dtype=np.float64)
        values = np.exp(-s * np.log(ns))
        np.cumsum(values, out=prefixes[start + 1:stop + 1])
        prefixes[start + 1:stop + 1] += prefixes[start]
    rows = []
    for p in MODULI:
        c = complex(mp.power(p, 1 - sm))
        total = 0j
        previous = 0
        observations = []
        for cells in CELL_CUTOFFS:
            cutoff = cells * p
            for start in range(previous, cutoff, CHUNK):
                stop = min(start + CHUNK, cutoff)
                ks = np.arange(start, stop, dtype=np.int64)
                weights = np.exp(-s.conjugate() * np.log(ks.astype(np.float64) + 1))
                tails = prefixes[ks] - c * prefixes[ks // p] - (1 - c) * z
                total += np.sum(tails * weights)
            # Previously observed complete-cell correction; explicitly conjectural.
            tail_model = (p * p - 1) / (12 * cutoff ** (2 * s.real))
            estimate = total - tail_model
            observations.append({
                "N": cutoff, "cells": cells, "raw": packed(total),
                "subtracted_tail_model": tail_model, "estimate": packed(estimate),
                "leading_normalized_error": packed(estimate / p ** alpha - constant),
                "after_leading": packed(estimate - constant * p ** alpha),
                "after_leading_and_G1": packed(estimate - constant * p ** alpha - abs(z) ** 2 * c),
            })
            previous = cutoff
        rows.append({"p": p, "amplitude": packed(c), "observations": observations})
    result = {"spec": spec, "s": packed(s), "height_65_digits": str(height),
              "zeta": packed(z), "K": packed(constant), "alpha": alpha,
              "rows": rows, "seconds": time.time() - started}
    print(spec["label"], "completed", round(result["seconds"], 2), flush=True)
    return result

def main():
    specs = [{"sigma": "0.5", "zero": j, "label": "zero-" + str(j)} for j in (1, 2, 3)]
    specs += [{"sigma": sigma, "zero": j, "label": "shift-" + sigma + "-" + str(j)}
              for sigma in ("0.65", "0.85") for j in (1, 2)]
    specs += [{"sigma": "0.5", "t": "17", "label": "line-nonzero"},
              {"sigma": "0.65", "t": "0", "label": "real-nonzero"}]
    started = time.time()
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(task, specs))
    with open("results.json", "w") as out:
        json.dump({"purpose": "Exploration only; no numerical proof claims", "workers": 4,
                   "moduli": MODULI, "cell_cutoffs": CELL_CUTOFFS, "chunk": CHUNK,
                   "python": platform.python_version(), "numpy": np.__version__,
                   "mpmath": mp.__version__, "seconds": time.time() - started,
                   "results": results}, out, indent=2)

if __name__ == "__main__":
    main()
