"""Runpod-only diagnostic of frozen prime-sieve phase conjectures J and K."""
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
import scipy
from scipy.special import zeta as hzeta

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


def phases(s, zs, factor, order):
    top = math.ceil(factor * abs(s.imag)) + 512
    n = np.arange(1, top + 1, dtype=np.int64)
    logs = np.log(n.astype(float))
    weights = np.exp(-s * logs)
    remainder = np.cumsum(weights) - zs - np.exp((1-s)*logs)/(1-s) - weights/2
    u = s.conjugate()
    norm = u*(u+1)
    literal = weights*np.conj(remainder)/norm
    rough = np.ones(top, dtype=bool)
    divisors = np.array([1.0])
    signs = np.array([1.0])
    coefficients = []
    for j in range(1, order+1):
        rising = complex(1)
        for r in range(2*j-1):
            rising *= u+r
        coefficients.append(-float(mp.bernoulli(2*j))*rising/math.factorial(2*j)/norm)
    rows = []
    for k in range(len(PRIMES)+1):
        if k:
            q = PRIMES[k-1]
            rough &= n % q != 0
            divisors = np.concatenate((divisors, q*divisors))
            signs = np.concatenate((signs, -signs))
        total = np.sum(literal[rough])
        cuts = np.floor(top/divisors)+1
        for j, coefficient in enumerate(coefficients, 1):
            exponent = 2*s.real+2*j-1
            tail = np.sum(signs*divisors**(-exponent)*hzeta(exponent, cuts))
            total += coefficient*tail
        rows.append([float(total.real), float(total.imag)])
    return rows


def task(index):
    mp.mp.dps = 55
    zero = mp.zetazero(index)
    height = float(mp.im(zero))
    controls = []
    for sigma in (0.45, 0.5, 0.55):
        s = complex(sigma, height)
        zs = complex(mp.zeta(mp.mpc(sigma, height)))
        a = np.array(phases(s, zs, 4, 8))
        b = np.array(phases(s, zs, 7, 12))
        limit = (0.5 - 1/(1-s.conjugate())-zs.conjugate())/(s.conjugate()*(s.conjugate()+1))
        controls.append({"sigma": sigma, "phases": b.tolist(),
            "configuration_difference": float(np.max(np.abs(a-b))),
            "unit_limit": [limit.real, limit.imag],
            "zeta_abs": abs(zs),
            "J_positive_indices": [k for k in range(len(b)) if b[k,1] > 1e-9],
            "K_decreasing_steps": [k for k in range(len(b)-1) if b[k+1,1]-b[k,1] < -1e-9]})
    return {"index":index, "height":height, "controls":controls}


if __name__ == "__main__":
    start = time.time()
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(task, range(1,97)))
    data = {"primes":PRIMES, "zero_count":96, "workers":8,
        "configurations":[[4,8],[7,12]], "threshold":1e-9,
        "versions":{"python":platform.python_version(), "numpy":np.__version__,
                    "scipy":scipy.__version__, "mpmath":mp.__version__},
        "seconds":time.time()-start, "results":results}
    with open("results.json", "w") as f:
        json.dump(data, f, indent=2)
    zeros = [(row, row["controls"][1]) for row in results]
    j = [(row["index"], k, c["phases"][k][1]) for row,c in zeros for k in c["J_positive_indices"]]
    k = [(row["index"], step, c["phases"][step+1][1]-c["phases"][step][1])
         for row,c in zeros for step in c["K_decreasing_steps"]]
    summary = {"seconds":data["seconds"], "J_violations":len(j), "K_violations":len(k),
        "J_examples":sorted(j,key=lambda x:-x[2])[:8],
        "K_examples":sorted(k,key=lambda x:x[2])[:8],
        "maximum_configuration_difference":max(c["configuration_difference"] for _,c in zeros)}
    with open("summary.json", "w") as f:
        json.dump(summary, f, indent=2)
    print(json.dumps(summary, indent=2), flush=True)
