"""Independent mesh and 80-digit residual checks on Runpod."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import pathlib, json, concurrent.futures
import numpy as np
import mpmath as mp
import kernel_reference as ex

OUT = pathlib.Path(__file__).resolve().parent


def check(task):
    n, m, C = task
    data = np.loadtxt(OUT/('coeff_N%d_m%d_C%d.csv' % task), delimiter=',', skiprows=1)
    a = data[:, 2]
    A, e, t, _ = ex.design(n, 52, True)
    r = A@a+e
    energy = float(r@r)
    # Probe log-spaced points plus locations carrying the largest mesh energy.
    order = np.argsort(np.abs(r[:-1]))[-24:]
    points = np.unique(np.r_[np.geomspace(1e-6/n, 30, 88), t[order]])
    approx = np.exp(-points)+ex.bose_h(points[:, None]*np.arange(1, n+1))@a
    mp.mp.dps = 80
    aa = [mp.mpf(float(x)) for x in a]
    discrepancies = []
    for x, y in zip(points, approx):
        z = mp.mpf(float(x))
        exact = mp.exp(-z)+mp.fsum(b*(1/(k*z)-1/mp.expm1(k*z))
                                 for k, b in enumerate(aa, 1))
        discrepancies.append(float(abs(exact-mp.mpf(float(y)))))
    return {'N': n, 'm': m, 'C': C, 'mesh_order': 52, 'l2_norm': float(np.sqrt(energy)),
            'fixed_prefix_exact': bool(np.array_equal(a[:m], ex.mobius(n)[1:m+1])),
            'max_abs_coefficient': float(np.max(np.abs(a))), 'mpmath_digits': 80,
            'point_count': len(points), 'max_residual_discrepancy': max(discrepancies)}


if __name__ == '__main__':
    tasks = [(n, n//4, C) for n in [128, 256, 512] for C in [1, 2]]+[(512, 8, C) for C in [1, 2]]
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        checks = list(pool.map(check, tasks))
    (OUT/'validation.json').write_text(json.dumps(checks, indent=2))
    print(json.dumps(checks, indent=2), flush=True)
