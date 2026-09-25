"""Independent Runpod-only check using the positive theta density itself.

This does not reuse the integration-by-parts moment formula in atom_hankel.py.
All output is exploratory; finite cutoffs and numerical quadrature are not proofs.
"""
import os
for variable in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[variable] = '1'
import json
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import mpmath as mp
from atom_hankel import analyze

PRECISION = 160
DEGREE = 12
ATOMS = 6

def direct_moment(job):
    j, n = job
    mp.mp.dps = PRECISION
    a = mp.pi*n*n
    # y = exp(2x), so this differs from the original x-quadrature both
    # in density formula and integration coordinate. The common 2*pi
    # normalization is omitted from every moment, as in atom_hankel.py.
    def integrand(y):
        return (mp.log(y)/2)**(2*j) * n*n * y**mp.mpf('.25') * (2*a*y-3)*mp.exp(-a*y)
    value = mp.quad(integrand, [1, mp.mpf('1.25'), mp.mpf('1.5'), 2, 3, 5, 10, 30, 100, 1000])
    return j, n, mp.nstr(value, PRECISION)

if __name__ == '__main__':
    jobs = [(j,n) for j in range(2*DEGREE+2) for n in range(1,ATOMS+1)]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as pool:
        values = list(pool.map(direct_moment,jobs))
    mp.mp.dps = PRECISION
    table = {(j,n):mp.mpf(value) for j,n,value in values}
    rows = [[table[j,n] for j in range(2*DEGREE+2)] for n in range(1,ATOMS+1)]
    report = dict(precision=PRECISION,degree=DEGREE,atoms=ATOMS,
                  raw_atoms=[[mp.nstr(x,PRECISION) for x in row] for row in rows],comparisons={})
    for count in [1,2,3,ATOMS]:
        raw = [sum(row[j] for row in rows[:count]) for j in range(2*DEGREE+2)]
        result = analyze(raw,DEGREE)
        report['comparisons'][str(count)] = result
        for block in result['blocks']:
            print('atoms',count,'degree',block['degree'],'min_eigen',block['min_eigenvalue'],flush=True)
    Path('direct-density-results.json').write_text(json.dumps(report,indent=2)+'\n')
