"""Run on Runpod: finite source interventions, never a Lean certificate."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from scipy.signal import fftconvolve
from scipy.special import gamma

MAX_POWER = 17
RS = [1.01, 1.05, 1.1, 1.25, 1.5]


def source(kind, seed, limit):
    prime = np.ones(limit + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, int(limit ** .5) + 1):
        if prime[p]:
            prime[p*p::p] = False
    primes = np.flatnonzero(prime)
    mu = np.ones(limit + 1, dtype=np.int64)
    mu[0] = 0
    for p in primes:
        mu[p::p] *= -1
        if p*p <= limit:
            mu[p*p::p*p] = 0
    rng = np.random.default_rng(seed)
    if kind == "shell_shuffle":
        for k in range(MAX_POWER + 2):
            ix = np.flatnonzero(mu[2**k:min(2**(k+1), limit+1)]) + 2**k
            mu[ix] = rng.permutation(mu[ix])
    elif kind == "random_multiplicative":
        mu = (mu != 0).astype(np.int64)
        for p, sign in zip(primes, rng.choice([-1, 1], len(primes))):
            if sign < 0:
                mu[p::p] *= -1
    return mu


def integer_convolution(a, b):
    raw = fftconvolve(a.astype(float), b.astype(float))
    nearest = np.rint(raw)
    return nearest.astype(np.int64), float(np.max(np.abs(raw-nearest)))


def run(spec):
    kind, seed = spec
    start = time.monotonic()
    mu = source(kind, seed, 2**(MAX_POWER+1))
    rows = []
    for k in range(8, MAX_POWER+1):
        n = 2**k
        a = mu[:n+1]
        b = mu[n+1:2*n+1]
        aa, e1 = integer_convolution(a, a)
        bb, e2 = integer_convolution(b, b)
        ab, e3 = integer_convolution(a, b)
        total, e4 = integer_convolution(mu[:2*n+1], mu[:2*n+1])
        # b[j] is the coefficient at the literal integer n+1+j.
        ka = np.arange(2, len(aa), dtype=np.longdouble)
        kb = np.arange(len(bb), dtype=np.longdouble) + 2*(n+1)
        kc = np.arange(len(ab), dtype=np.longdouble) + n+1
        kt = np.arange(2, len(total), dtype=np.longdouble)
        for r in RS:
            fac = np.longdouble(gamma(r))
            ea = fac*np.sum(aa[2:]*ka**(-r), dtype=np.longdouble)
            eb = fac*np.sum(bb*kb**(-r), dtype=np.longdouble)
            cross = fac*np.sum(ab*kc**(-r), dtype=np.longdouble)
            et = fac*np.sum(total[2:]*kt**(-r), dtype=np.longdouble)
            rows.append(dict(kind=kind, seed=seed, N=n, r=r,
                prefix=float(ea), block=float(eb), cross=float(cross), total=float(et),
                normalized_cross=float(cross/np.sqrt(ea*eb)),
                relative_increment=float((et-ea)/ea),
                balance_error=float(et-ea-eb-2*cross),
                fft_rounding_error=max(e1,e2,e3,e4)))
    return dict(kind=kind, seed=seed, seconds=time.monotonic()-start, rows=rows)


if __name__ == "__main__":
    start = time.monotonic()
    jobs = [("literal", 0)] + [(kind, seed) for kind in
        ("shell_shuffle", "random_multiplicative") for seed in (101,202,303,404)]
    with ProcessPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, jobs))
    out = dict(experiment="H1", seconds=time.monotonic()-start,
        formula="Gamma(r) sum mu(m) mu(n)/(m+n)^r", results=results)
    with open("mobius-results.json", "w") as f:
        json.dump(out, f, indent=2)
    for result in results:
        rows = result["rows"]
        print(result["kind"], result["seed"], "positive_cross", sum(x["cross"]>0 for x in rows),
            "/", len(rows), "cross_range", min(x["cross"] for x in rows), max(x["cross"] for x in rows), flush=True)
    print("seconds", out["seconds"], flush=True)
