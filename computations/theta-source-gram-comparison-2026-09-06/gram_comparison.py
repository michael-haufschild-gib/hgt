"""Runpod-only diagnostic of a proposed raw-source Gram representation.

Reuses archived direct-density moments; no new quadrature or Lean certificates.
Parallelizes independent shell cutoffs, with one native math thread per worker.
"""
import os
for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name] = '1'
import argparse
import json
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import mpmath as mp


def analyze(job):
    count, source, precision, degree = job
    mp.mp.dps = precision
    rows = source['raw_atoms'][:count]
    raw = [sum(mp.mpf(row[j]) for row in rows) for j in range(2*degree+2)]
    mu = [x/raw[0] for x in raw]
    c = [(-1)**j*mu[j]/mp.factorial(2*j) for j in range(len(mu))]
    moments = []
    for k in range(2*degree+1):
        moments.append(-2*(k+1)*c[k+1]-sum(c[j]*moments[k-j] for j in range(1,k+1)))
    blocks = []
    for d in range(1, degree+1):
        B = mp.matrix(d+1)
        D = mp.matrix(d+1)
        for i in range(d+1):
            for j in range(d+1):
                n = i+j+1
                B[i,j] = 2*sum((n-2*k)*mu[n-k]*mu[k]/(mp.factorial(2*(n-k))*mp.factorial(2*k))
                               for k in range(min(i,j)+1))
                D[i,j] = mu[n]/(mp.factorial(2*i+1)*mp.factorial(2*j+1))
        # Independent check: multiplication by F is triangular congruence.
        H = mp.matrix([[moments[i+j] for j in range(d+1)] for i in range(d+1)])
        T = mp.matrix([[c[i-j] if i >= j else 0 for j in range(d+1)] for i in range(d+1)])
        S = mp.diag([(-1)**i for i in range(d+1)])
        residual = mp.norm(B-S*T*H*T.T*S)
        # Whitening converts the generalized B/D spectrum to a symmetric problem.
        scale = mp.diag([1/mp.sqrt(D[i,i]) for i in range(d+1)])
        Ds = scale*D*scale
        Bs = scale*B*scale
        L = mp.cholesky(Ds)
        Linv = L**-1
        W = Linv*Bs*Linv.T
        W = (W+W.T)/2
        eigen, vectors = mp.eigsy(W)
        out = dict(degree=d,
                   eigenvalues=[mp.nstr(x,60) for x in eigen],
                   congruence_residual=mp.nstr(residual,10))
        for label,index in [('least',0),('greatest',d)]:
            v = vectors[:,index]
            a = scale*Linv.T*v
            a /= max(abs(x) for x in a)
            out[label+'_witness'] = [mp.nstr(x,60) for x in a]
            out[label+'_B'] = mp.nstr((a.T*B*a)[0],60)
            out[label+'_D'] = mp.nstr((a.T*D*a)[0],60)
        blocks.append(out)
    return str(count), blocks


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('input')
    parser.add_argument('--precision',type=int,default=130)
    parser.add_argument('--degree',type=int,default=12)
    parser.add_argument('--output',default='gram-comparison-results.json')
    args = parser.parse_args()
    source = json.loads(Path(args.input).read_text())
    counts = sorted(set([1,2,3,len(source['raw_atoms'])]))
    jobs = [(n,source,args.precision,args.degree) for n in counts]
    with ProcessPoolExecutor(max_workers=min(len(jobs),os.cpu_count() or 1)) as pool:
        comparisons = dict(pool.map(analyze,jobs))
    result = dict(precision=args.precision,degree=args.degree,input=args.input,
                  input_precision=source.get('precision',source.get('settings',{}).get('precision')),
                  comparisons=comparisons)
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    for n,blocks in comparisons.items():
        for b in blocks:
            print(n,b['degree'],b['eigenvalues'][0],b['eigenvalues'][-1],flush=True)
