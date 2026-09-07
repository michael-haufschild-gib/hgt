"""Runpod-only mechanism discrimination; no numerical premise for Lean."""
import json
import math
import os
import platform
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["MKL_NUM_THREADS"] = "1"
import mpmath as mp


def derivative_polynomials(order):
    # R_n = 2^n P_n, P_0=4q^2-6q.
    # R_(n+1)=(1-4q)R_n+4q R_n'.
    rows = [[0, -6, 4]]
    for _ in range(order):
        old = rows[-1]
        new = [0] * (len(old) + 1)
        for k, c in enumerate(old):
            new[k] += (1 + 4*k) * c
            new[k+1] -= 4*c
        rows.append(new)
    return rows


def derivatives(x, atoms, polynomials):
    q = mp.pi * mp.exp(2*x)
    nodes = [n*n*q for n in range(1, atoms+1)]
    weights = [mp.exp(q-z) for z in nodes]
    values = [mp.fsum(w * mp.polyval(list(reversed(p)), z)
                      for w, z in zip(weights, nodes)) / mp.mpf(2)**k
              for k, p in enumerate(polynomials)]
    return q, values


def transition(atoms, polynomials, digits):
    def carrier(x):
        _, d = derivatives(x, atoms, polynomials[:2])
        return 3 + 2*x*d[1]/d[0]
    lo, hi = mp.mpf("0.1"), mp.mpf("0.5")
    assert carrier(lo) > 0 and carrier(hi) < 0
    tolerance = mp.mpf(10)**(-digits+30)
    for _ in range(4*digits):
        mid = (lo+hi)/2
        if carrier(mid) > 0:
            lo = mid
        else:
            hi = mid
        if hi-lo < tolerance:
            break
    assert hi-lo < tolerance
    x = (lo+hi)/2
    return x, carrier(x), hi-lo


def parity_probe(moments, parity, cap):
    raw = mp.matrix([[moments[i+j+parity] for j in range(cap)] for i in range(cap)])
    scales = [mp.sqrt(abs(raw[i, i])) if raw[i, i] else mp.mpf(1) for i in range(cap)]
    matrix = mp.matrix([[raw[i, j]/(scales[i]*scales[j]) for j in range(cap)]
                        for i in range(cap)])
    lower = mp.eye(cap)
    pivots = []
    for i in range(cap):
        pivot = matrix[i, i] - mp.fsum(lower[i, k]**2*pivots[k] for k in range(i))
        pivots.append(pivot)
        if pivot <= 0:
            head = mp.matrix([[matrix[j, k] for k in range(i)] for j in range(i)])
            border = mp.matrix([matrix[j, i] for j in range(i)])
            v = list(-mp.lu_solve(head, border)) + [mp.mpf(1)] if i else [mp.mpf(1)]
            first = mp.matrix([[matrix[j, k] for k in range(i+1)] for j in range(i+1)])
            quadratic = mp.fsum(v[j]*first[j, k]*v[k]
                                for j in range(i+1) for k in range(i+1))
            eigmin = min(mp.eigsy(first, eigvals_only=True))
            return {"first_nonpositive_size": i+1,
                    "pivots": [mp.nstr(z, 70) for z in pivots],
                    "scaled_min_eigenvalue": mp.nstr(eigmin, 70),
                    "scaled_witness": [mp.nstr(z, 70) for z in v],
                    "witness_quadratic": mp.nstr(quadratic, 70),
                    "status": "negative" if pivot < 0 and quadratic < 0 and eigmin < 0
                              else "inconclusive"}
        for j in range(i+1, cap):
            lower[j, i] = (matrix[j, i] - mp.fsum(
                lower[j, k]*lower[i, k]*pivots[k] for k in range(i))) / pivot
    return {"status": "positive_pivots_through_cap", "cap": cap,
            "pivots": [mp.nstr(z, 70) for z in pivots]}


def worker(job):
    label, digits, atoms = job
    started = time.monotonic()
    mp.mp.dps = digits
    cap = 10
    polynomials = derivative_polynomials(4*cap-2)
    x, residual, width = transition(atoms, polynomials, digits)
    q, d = derivatives(x, atoms, polynomials)
    d = [v/d[0] for v in d]
    moments = [(-1)**k * mp.fsum((-1)**i * math.comb(2*k, i) * d[i]*d[2*k-i]
                               for i in range(2*k+1)) / (32*q)**k
               for k in range(2*cap)]
    return {"label": label, "digits": digits, "atoms": atoms,
            "transition": mp.nstr(x, 90), "transition_width": mp.nstr(width, 20),
            "carrier_residual": mp.nstr(residual, 20), "q": mp.nstr(q, 70),
            "even": parity_probe(moments, 0, cap),
            "odd": parity_probe(moments, 1, cap),
            "seconds": time.monotonic()-started}


if __name__ == "__main__":
    started = time.monotonic()
    jobs = [("literal_approx_120_12", 120, 12),
            ("literal_approx_200_20", 200, 20),
            ("first_atom_control", 200, 1)]
    with ProcessPoolExecutor(max_workers=3) as pool:
        rows = list(pool.map(worker, jobs, chunksize=1))
    output = {"scope": "Diagnostic finite sums only; no certified infinite tail or Lean sign premise.",
              "workers": 3, "cpu_count": os.cpu_count(), "python": platform.python_version(),
              "mpmath": mp.__version__, "seconds": time.monotonic()-started, "rows": rows}
    Path("results.json").write_text(json.dumps(output, indent=2)+"\n")
    print(json.dumps(output, indent=2), flush=True)
