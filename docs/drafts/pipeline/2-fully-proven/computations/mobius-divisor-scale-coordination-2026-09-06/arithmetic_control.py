"""Finite rough-part sign ensembles. Run only on the specified Runpod."""
import json
import multiprocessing as mp
import os
from pathlib import Path
import sys
import time

os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
import numpy as np

ROOT = Path(__file__).resolve().parent
CUTOFFS = [1, 2, 3, 5, 11, 31]
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def endpoint(M):
    d = np.arange(1, M+1, dtype=np.int64)
    q = M // d
    edge = (M-d*q)/(np.sqrt(float(M))+np.sqrt(d*q))
    c = MU[1:M+1] * (np.sqrt(d)*ABEL[q-1]+DEFECT[q]*edge)/M
    rough = d.copy()
    values = []
    processed = 0
    for y in CUTOFFS:
        for p in PRIMES:
            if processed < p <= y:
                # Non-squarefree entries carry zero weight, so one division suffices.
                rough[p-1::p] //= p
        processed = y
        fibers = np.bincount(rough, weights=c, minlength=M+1)
        values.append(float(np.dot(fibers, fibers)))
    direct = DIRECT[M-1]/M
    return dict(M=M, actual=direct, ensembles=values,
                identity_residual=float(c.sum()-direct))


if __name__ == "__main__":
    phase = sys.argv[1]
    assert phase in ("discovery", "validation")
    started = time.monotonic()
    with np.load(ROOT / "source.npz") as data:
        MU, DEFECT, ABEL, DIRECT = (data[k] for k in ("mu", "defect", "abel", "direct"))
    exponents = [12, 14, 16] if phase == "discovery" else [18, 20]
    bands = []
    with mp.get_context("fork").Pool(8) as pool:
        for e in exponents:
            rows = pool.map(endpoint, [2**e+i*2**(e-6) for i in range(0, 64, 4)])
            actual = float(np.mean([r["actual"]**2 for r in rows]))
            means = np.mean([r["ensembles"] for r in rows], axis=0)
            ratios = means/actual
            bands.append(dict(exponent=e, actual_mean_square=actual,
                              ensemble_mean_squares=means.tolist(), ratios=ratios.tolist(),
                              C2_pass=bool(ratios[-1] >= 4), rows=rows))
    report = dict(phase=phase, cutoffs=CUTOFFS, seconds=time.monotonic()-started, bands=bands)
    (ROOT / ("arithmetic-"+phase+".json")).write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(phase=phase, seconds=report["seconds"],
                         bands=[{k:v for k,v in b.items() if k != "rows"} for b in bands]), indent=2))
