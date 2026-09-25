#!/usr/bin/env python3
"""Finite flat-source normalization discriminator; numerical evidence, not proof.

Run only on the authorized RunPod. BLAS is single-threaded per process;
independent seeded fits use available CPU affinity, capped at 16 workers.
"""
import os
for name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS",
             "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[name] = "1"

import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import platform
import time
import numpy as np
from scipy.optimize import least_squares
import scipy


def comm(a, b):
    return a @ b - b @ a


def frame(n, rank, rng):
    q, _ = np.linalg.qr(rng.normal(size=(n, n)) + 1j*rng.normal(size=(n, n)))
    return q


def chart(x, u, rank, derivatives=False):
    n = len(u)
    size = (n-rank)*rank
    bottom = (x[:size] + 1j*x[size:]).reshape(n-rank, rank)
    v = u @ np.vstack((np.eye(rank), bottom))
    right = np.linalg.solve(v.conj().T @ v, v.conj().T)
    p = v @ right
    if not derivatives:
        return p
    directions = []
    complement = np.eye(n)-p
    for j in range(2*size):
        dv = np.zeros((n, rank), complex)
        row, col = divmod(j % size, rank)
        dv[rank+row, col] = 1 if j < size else 1j
        term = complement @ u @ dv @ right
        directions.append(term+term.conj().T)
    return p, directions


def vector(a):
    return np.r_[a.real.ravel(), a.imag.ravel()]


def matrices(a):
    return {"real": a.real.tolist(), "imag": a.imag.tolist()}


def job(spec):
    n, rank, seed = spec
    rng = np.random.default_rng(seed)
    p = np.diag([1.0]*rank+[0.0]*(n-rank)).astype(complex)
    uq, ur = frame(n, rank, rng), frame(n, rank, rng)
    width = 2*(n-rank)*rank

    def evaluate(x, jac=False):
        if jac:
            q, dq = chart(x[:width], uq, rank, True)
            r, dr = chart(x[width:], ur, rank, True)
        else:
            q = chart(x[:width], uq, rank)
            r = chart(x[width:], ur, rank)
        s = p+q+r
        k = comm(p, q)+comm(q, r)+comm(r, p)
        if not jac:
            return vector(comm(s, k))
        cols = []
        for d in dq:
            dk = comm(p, d)+comm(d, r)
            cols.append(vector(comm(d, k)+comm(s, dk)))
        for d in dr:
            dk = comm(q, d)+comm(d, p)
            cols.append(vector(comm(d, k)+comm(s, dk)))
        return np.array(cols).T

    start = time.time()
    x0 = np.zeros(2*width)
    # Check analytic Jacobian against a directional central difference.
    direction = rng.normal(size=len(x0))
    direction /= np.linalg.norm(direction)
    eps = 1e-6
    finite = (evaluate(x0+eps*direction)-evaluate(x0-eps*direction))/(2*eps)
    analytic = evaluate(x0, True) @ direction
    jac_error = float(np.linalg.norm(finite-analytic))
    fit = least_squares(evaluate, x0, jac=lambda x: evaluate(x, True),
                        ftol=1e-12, xtol=1e-12, gtol=1e-12, max_nfev=400)
    q, r = chart(fit.x[:width], uq, rank), chart(fit.x[width:], ur, rank)
    s = p+q+r
    k = comm(p, q)+comm(q, r)+comm(r, p)
    b = 3*np.eye(n)-s
    f = k @ (3*k@k+s@s@b@b)
    flat = float(np.linalg.norm(comm(s, k)))
    jsv = np.linalg.svd(evaluate(fit.x, True), compute_uv=False)
    return {"dimension": n, "rank_each": rank, "seed": seed,
            "seconds": time.time()-start, "nfev": fit.nfev,
            "optimizer_success": bool(fit.success), "status": int(fit.status),
            "flat_residual_fro": flat,
            "projection_residual_fro": max(float(np.linalg.norm(t@t-t)) for t in (p,q,r)),
            "selfadjoint_residual_fro": max(float(np.linalg.norm(t-t.conj().T)) for t in (p,q,r)),
            "jacobian_directional_error": jac_error,
            "current_norm_fro": float(np.linalg.norm(k)),
            "candidate_polynomial_residual_fro": float(np.linalg.norm(f)),
            "aggregate_eigenvalues": np.linalg.eigvalsh(s).tolist(),
            "flat_jacobian_singular_values": jsv.tolist(),
            "P": matrices(p), "Q": matrices(q), "R": matrices(r)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    specs = [(n, rank, 52000+100*n+i) for n, rank in ((2,1),(3,1),(4,2),(6,3))
             for i in range(8)]
    workers = min(16, len(os.sched_getaffinity(0)), len(specs))
    start = time.time()
    results = []
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for result in pool.map(job, specs):
            results.append(result)
            print(json.dumps({key: result[key] for key in (
                "dimension", "seed", "flat_residual_fro",
                "candidate_polynomial_residual_fro", "seconds")}), flush=True)
    output = {"purpose": "CFC-1 normalization discriminator, not arithmetic source admission",
              "python": platform.python_version(), "numpy": np.__version__,
              "scipy": scipy.__version__, "workers": workers,
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "seconds": time.time()-start, "results": results}
    Path(args.output).write_text(json.dumps(output, indent=2)+"\n")


if __name__ == "__main__":
    main()
