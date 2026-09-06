"""Exploratory floating-point minimax gaps; no proof certificates. Run on Runpod."""
import os
for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[name] = '1'
import json
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from numpy.polynomial.chebyshev import chebvander, chebval, chebder
from scipy.optimize import linprog, root


def one(job):
    m, grid = job
    c = (1 - np.cos(np.linspace(0, np.pi, grid))) / 2
    x = c * (2-c)
    v = c[:, None]**m * chebvander(2*x-1, m)
    mat = np.vstack((np.column_stack((v[:, :m], -np.ones(grid))),
                     np.column_stack((-v[:, :m], -np.ones(grid)))))
    rhs = np.concatenate((-v[:, m], v[:, m]))
    sol = linprog(np.r_[np.zeros(m), 1.], A_ub=mat, b_ub=rhs,
                  bounds=[(None, None)]*m+[(0, None)], method='highs',
                  options={'primal_feasibility_tolerance': 1e-9,
                           'dual_feasibility_tolerance': 1e-9})
    if not sol.success:
        return {'m': m, 'grid': grid, 'error': sol.message}
    a = np.r_[sol.x[:m], 1.]

    def value(z, aa):
        return z**m * chebval(2*z*(2-z)-1, aa)

    def deriv(z, aa):
        t = 2*z*(2-z)-1
        return m*z**(m-1)*chebval(t, aa) + z**m*(4-4*z)*chebval(t, chebder(aa))

    f = value(c, a)
    peaks = np.flatnonzero((np.abs(f[1:-1]) >= np.abs(f[:-2])) &
                           (np.abs(f[1:-1]) >= np.abs(f[2:])))+1
    peaks = sorted(peaks, key=lambda i: -abs(f[i]))[:m]
    nodes = np.sort(c[peaks])
    refined = False
    if len(nodes) == m:
        signs = (-1.)**np.arange(m, -1, -1)

        def equations(z):
            aa = np.r_[z[:m], 1.]
            tt = z[m]
            zz = z[m+1:]
            return np.r_[value(np.r_[zz, 1.], aa)-signs*tt, deriv(zz, aa)]

        rr = root(equations, np.r_[a[:m], sol.x[-1], nodes], tol=1e-11)
        if rr.success and np.max(np.abs(equations(rr.x))) < 1e-8:
            a = np.r_[rr.x[:m], 1.]
            nodes = rr.x[m+1:]
            refined = bool(np.all(np.diff(nodes)>0) and nodes[0]>0 and nodes[-1]<1)
    fine = np.linspace(0, 1, 100001)
    peak = float(np.max(np.abs(value(fine, a))))
    penult = a[0]-a[1] if m == 1 else 2.**(2*m-3)*a[m-1]-m*2.**(2*m-2)
    delta = peak / (4.**(m-1)*abs(penult))
    return {'m':m, 'grid':grid, 'lp_norm':float(sol.x[-1]), 'dense_norm':peak,
            'delta':delta, 'a':a.tolist(), 'contacts':nodes.tolist(), 'refined':refined,
            'value_at_contacts':value(np.r_[nodes,1.],a).tolist()}


if __name__ == '__main__':
    jobs = [(m, grid) for m in range(1, 9) for grid in (1001, 4001, 12001)]
    with ProcessPoolExecutor(max_workers=24) as pool:
        results = list(pool.map(one, jobs))
    best = [next(r for r in results if r['m']==m and r['grid']==12001) for m in range(1,9)]
    gaps = np.array([r['delta'] for r in best])
    ratios = gaps[1:]/gaps[:-1]
    # Scaling moments by a geometric factor preserves Hankel positivity and
    # improves conditioning. These eigenvalues are exploratory only.
    moments = (gaps/gaps[0])**2
    scale = ratios[-1]**2
    scaled = moments/scale**np.arange(len(moments))
    hankel = {}
    for shift in (0,1):
        for size in (2,3,4):
            if 2*(size-1)+shift < len(scaled):
                h = np.array([[scaled[i+j+shift] for j in range(size)] for i in range(size)])
                hankel[f'{shift}:{size}'] = np.linalg.eigvalsh(h).tolist()
    out={'results':results,'best':best,'ratios':ratios.tolist(),
         'logconvex_ratios':(ratios[1:]/ratios[:-1]).tolist(),
         'moment_geometric_scale':float(scale),'scaled_hankel_eigenvalues':hankel}
    with open('minimax-results.json','w') as stream:
        json.dump(out,stream,indent=2)
    print(json.dumps({k:v for k,v in out.items() if k not in ('results','best')},indent=2))
