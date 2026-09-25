"""Complete finite prime-aperture profile; Runpod only."""
import json
import multiprocessing as mp
import os
from pathlib import Path
import time

os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
import numpy as np

ROOT = Path(__file__).resolve().parent


def endpoint(M):
    d = np.arange(1, M+1, dtype=np.int64)
    q = M//d
    c = MU[1:M+1]*(np.sqrt(d)*ABEL[q-1]+DEFECT[q]*(M-d*q)/
                   (np.sqrt(float(M))+np.sqrt(d*q)))/M
    rough = d.copy()
    cutoffs = sorted(set([y for y in [1,2,3,5,7,11]+[2**k for k in range(4,22)] if y<M]+[M]))
    rows, last, before_five = [], 0, None
    for y in cutoffs:
        for p0 in PRIMES[(PRIMES>last)&(PRIMES<=y)]:
            p = int(p0)
            rough[p-1::p] //= p
        last = y
        fibers = np.bincount(rough, weights=c, minlength=M+1)
        total = float(np.dot(fibers, fibers))
        mean = float(fibers[1])
        rows.append(dict(y=y, ensemble=total, smooth_mean=mean,
                         noise_variance=total-mean*mean))
        if y == 3:
            before_five = fibers.copy()
        if y == 5:
            r = np.arange(1, M//5+1)
            r = r[r%5 != 0]
            cross = float(2*np.dot(before_five[r], before_five[5*r]))
            assert abs(total-np.dot(before_five,before_five)-cross) < 1e-12
    actual = float(DIRECT[M-1]/M)
    assert abs(rows[-1]["ensemble"]-actual**2) < 1e-12
    return dict(M=M, actual=actual, peak_recorded_y=max(rows,key=lambda r:r["ensemble"])["y"], rows=rows)


if __name__ == "__main__":
    started = time.monotonic()
    with np.load(ROOT / "source.npz") as data:
        MU, DEFECT, ABEL, DIRECT = (data[k] for k in ("mu","defect","abel","direct"))
        PRIMES = np.flatnonzero(data["tau"] == 2)
    endpoints = [2**e+i*2**(e-6) for e in (12,16,20) for i in (0,16,32,48)]
    with mp.get_context("fork").Pool(8) as pool:
        rows = pool.map(endpoint,endpoints)
    report = dict(seconds=time.monotonic()-started, endpoints=rows)
    (ROOT/"aperture.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(seconds=report["seconds"], peaks=[dict(M=r["M"],y=r["peak_recorded_y"]) for r in rows]),indent=2))
