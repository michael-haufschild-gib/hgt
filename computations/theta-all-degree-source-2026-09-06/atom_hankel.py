"""Exploratory Runpod-only theta cumulant/Hankel comparison, not a proof.

Parallel jobs are independent raw-moment integrals. No zero tables are used.
"""
import os
for env in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[env] = '1'
import argparse
import json
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import mpmath as mp


def moment(job):
    j, n, precision = job
    mp.mp.dps = precision
    nn = mp.mpf(n)
    def rho(x):
        return nn**2 * mp.exp(mp.mpf('2.5')*x-mp.pi*nn**2*mp.exp(2*x))
    if j == 0:
        fun = rho
    else:
        fun = lambda x: (4*j*x**(2*j-1)-x**(2*j))*rho(x)
    # Beyond six the source is far below the working precision. This is an
    # exploratory truncation, never an asserted theorem about the tail.
    value = mp.quad(fun, [0, mp.mpf('0.125'), mp.mpf('0.25'),
                         mp.mpf('0.5'), 1, 2, 3, 6])
    if j == 0:
        value = 2*nn**2*mp.exp(-mp.pi*nn**2)-value
    return j, n, mp.nstr(value, precision)


def analyze(raw, degree):
    c = [(-1)**j * m / raw[0] / mp.factorial(2*j) for j, m in enumerate(raw)]
    moments = []
    for k in range(2*degree+1):
        moments.append(-2*(k+1)*c[k+1] - sum(c[j]*moments[k-j] for j in range(1,k+1)))
    scale = moments[1]/moments[0]
    s = [v / (moments[0]*scale**k) for k, v in enumerate(moments)]
    blocks = []
    for d in range(1,degree+1):
        h = mp.matrix([[s[i+j] for j in range(d+1)] for i in range(d+1)])
        values, vectors = mp.eigsy(h)
        head = h[:d,:d]
        column = h[:d,d]
        q = list(-mp.lu_solve(head, column)) + [mp.mpf(1)]
        val = (mp.matrix(q).T*h*mp.matrix(q))[0]
        blocks.append(dict(degree=d, determinant=mp.nstr(mp.det(h), 45),
                           min_eigenvalue=mp.nstr(values[0],45),
                           schur_value=mp.nstr(val,45),
                           monic_schur_polynomial=[mp.nstr(x,45) for x in q]))
    return dict(moments=[mp.nstr(x,60) for x in moments],
                scale=mp.nstr(scale,60), blocks=blocks)


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--degree',type=int,default=6)
    parser.add_argument('--precision',type=int,default=90)
    parser.add_argument('--atoms',type=int,default=8)
    parser.add_argument('--output',default='atom-hankel-results.json')
    args=parser.parse_args()
    jobs=[(j,n,args.precision) for j in range(2*args.degree+2)
          for n in range(1,args.atoms+1)]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as pool:
        results=list(pool.map(moment,jobs))
    mp.mp.dps=args.precision
    data={(j,n):mp.mpf(value) for j,n,value in results}
    by_atom=[[data[j,n] for j in range(2*args.degree+2)]
             for n in range(1,args.atoms+1)]
    report=dict(settings=vars(args),raw_atoms=[[mp.nstr(x,args.precision) for x in row] for row in by_atom],comparisons={})
    for count in [1,2,3,args.atoms]:
        raw=[sum(row[j] for row in by_atom[:count]) for j in range(2*args.degree+2)]
        report['comparisons'][str(count)]=analyze(raw,args.degree)
    Path(args.output).write_text(json.dumps(report,indent=2)+'\n')
    for count,result in report['comparisons'].items():
        for block in result['blocks']:
            print('atoms',count,'degree',block['degree'],'min_eigen',block['min_eigenvalue'],
                  'Schur',block['schur_value'],flush=True)
