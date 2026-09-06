"""Exact finite arithmetic source; all numerical execution belongs on Runpod."""
import argparse
import hashlib
import json
import multiprocessing as mp
import os
from pathlib import Path
import time

os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
import numpy as np
from scipy.special import gammaln

ROOT = Path(__file__).resolve().parent
GAMMA = 0.577215664901532860606512090082402431


def prepare(limit):
    started = time.monotonic()
    prime_mask = np.ones(limit + 1, dtype=bool)
    prime_mask[:2] = False
    for p in range(2, int(limit ** 0.5) + 1):
        if prime_mask[p]:
            prime_mask[p*p::p] = False
    primes = np.flatnonzero(prime_mask)
    mu = np.ones(limit + 1, dtype=np.int8)
    mu[0] = 0
    tau = np.ones(limit + 1, dtype=np.int32)
    tau[0] = 0
    lam = np.zeros(limit + 1)
    for p0 in primes:
        p = int(p0)
        mu[p::p] *= -1
        mu[p*p::p*p] = 0
        tau[p::p] *= 2
        lam[p] = np.log(p)
        power, exponent = p*p, 2
        while power <= limit:
            tau[power::power] = tau[power::power] // exponent * (exponent + 1)
            lam[power] = np.log(p)
            power *= p
            exponent += 1
    n = np.arange(limit + 1, dtype=np.float64)
    divisor_sum = np.cumsum(tau, dtype=np.int64)
    defect = gammaln(n + 1) - divisor_sum + 2 * GAMMA * n
    roots = np.sqrt(n)
    weights = 1 / (np.sqrt(n[1:] + 1) + roots[1:])
    abel = np.concatenate(([0.0], np.cumsum(defect[1:] * weights)))
    psi = np.cumsum(lam)
    direct = np.concatenate(([0.0], np.cumsum((psi[1:] - n[1:] + 2 * GAMMA) * weights)))
    np.savez(ROOT / "source.npz", mu=mu, tau=tau, defect=defect, abel=abel,
             direct=direct, psi=psi)
    metadata = dict(limit=limit, prime_count=len(primes), seconds=time.monotonic()-started,
                    numpy=np.__version__, workers=8,
                    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT / "metadata.json").write_text(json.dumps(metadata, indent=2)+"\n")
    return metadata


def endpoint(M):
    d = np.arange(1, M + 1, dtype=np.int64)
    q = M // d
    # Cancellation-free form of sqrt(M)-sqrt(d*q).
    edge = (M - d*q) / (np.sqrt(float(M)) + np.sqrt(d*q))
    channel = MU[1:M+1] * (np.sqrt(d) * ABEL[q-1] + DEFECT[q] * edge) / M
    groups = np.floor(np.log2(q)).astype(np.int32)
    row = np.bincount(groups, weights=channel, minlength=22)
    direct = DIRECT[M-1] / M
    residual = float(row.sum() - direct)
    if abs(residual) > 5e-10:
        raise ArithmeticError((M, residual))
    return M, row, direct, float(np.abs(channel).sum()), residual


def summarize(rows, exponent):
    M = np.array([x[0] for x in rows])
    G = np.stack([x[1] for x in rows])
    direct = np.array([x[2] for x in rows])
    center = G - G.mean(axis=0)
    cov = center.T @ center / len(rows)
    diagonal = float(np.trace(cov))
    full = float(np.var(G.sum(axis=1)))
    cancellation = diagonal - full
    by_distance = [float(2*np.diag(cov, k).sum()) for k in range(1, len(cov))]
    adjacent = -by_distance[0] / cancellation if cancellation > 0 else None
    rng = np.random.default_rng(20260906)
    shuffled = []
    for _ in range(512):
        total = sum(rng.permutation(G[:, j]) for j in range(G.shape[1]))
        shuffled.append(float(np.var(total)))
    np.savez(ROOT / ("rows-e%d.npz" % exponent), M=M, groups=G, direct=direct,
             channel_abs_mass=[x[3] for x in rows], residual=[x[4] for x in rows],
             covariance=cov, shuffled_variances=shuffled)
    result = dict(exponent=exponent, samples=len(rows), M_min=int(M.min()), M_max=int(M.max()),
                  max_identity_residual=max(abs(x[4]) for x in rows),
                  diagonal_variance=diagonal, full_variance=full,
                  full_over_diagonal=full/diagonal, adjacent_cancellation_share=adjacent,
                  C1_pass=adjacent is not None and adjacent >= 0.75,
                  covariance_by_distance=by_distance,
                  raw_mean_square=float(np.mean(G.sum(axis=1)**2)),
                  max_abs_full=float(np.abs(G.sum(axis=1)).max()),
                  max_group_abs=float(np.abs(G).max()),
                  control_variance_quantiles=np.quantile(shuffled, [0, .05, .5, .95, 1]).tolist())
    return result


def run(phase):
    global MU, DEFECT, ABEL, DIRECT
    started = time.monotonic()
    with np.load(ROOT / "source.npz") as data:
        MU, DEFECT, ABEL, DIRECT = (data[k] for k in ("mu", "defect", "abel", "direct"))
    exponents = [12, 14, 16] if phase == "discovery" else [18, 20]
    results = []
    with mp.get_context("fork").Pool(8) as pool:
        for e in exponents:
            endpoints = [2**e + i*2**(e-6) for i in range(64)]
            rows = pool.map(endpoint, endpoints)
            results.append(summarize(rows, e))
    report = dict(phase=phase, seconds=time.monotonic()-started, bands=results)
    (ROOT / (phase + ".json")).write_text(json.dumps(report, indent=2)+"\n")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=["prepare", "discovery", "validation"])
    args = parser.parse_args()
    result = prepare(2**21) if args.action == "prepare" else run(args.action)
    print(json.dumps(result, indent=2))
