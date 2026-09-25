"""Reverse prime/cofactor sum and test dyadic-charge-preserving interventions."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import json
import argparse
import math
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import numpy as np
from experiment import primes_to

POWER = 23
NMAX = 2**POWER


def trial(seed):
    # Independent circular shifts inside each dyadic cofactor block preserve
    # exactly its sign count and charge, but usually destroy multiplicativity.
    out=[]
    for n in cutoffs:
        rng = np.random.default_rng(seed)
        shifted = f[:n+1].copy()
        for k in range(2, int(math.log2(n))+1):
            lo, hi = 2**k, min(n+1,2**(k+1))
            shifted[lo:hi] = np.roll(f[lo:hi], int(rng.integers(hi-lo)))
        out.append(float(np.dot(shifted[1:], kernels[n])))
    return out


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--power',type=int,default=23)
    parser.add_argument('--cutoffs',type=int,nargs='+',default=[2**k for k in (15,17,19,21,23)])
    parser.add_argument('--seed',type=int,default=75100)
    parser.add_argument('--count',type=int,default=64)
    parser.add_argument('--output',default='reverse-results.json')
    args=parser.parse_args()
    POWER=args.power
    NMAX=2**POWER
    start=time.monotonic()
    primes=primes_to(NMAX)
    f=np.ones(NMAX+1,dtype=np.int8)
    f[0]=0
    for pp in primes:
        pk=int(pp)
        while pk<=NMAX:
            f[pk::pk]*=-1
            pk*=int(pp)
    theta=np.zeros(NMAX+1)
    theta[primes]=np.log(primes)
    theta=np.cumsum(theta)
    sums=np.cumsum(f,dtype=np.int64)
    cutoffs=args.cutoffs
    kernels={}
    rows=[]
    for n in cutoffs:
        m=np.arange(1,n+1,dtype=np.int64)
        kernel=theta[n//m]-n/m
        kernels[n]=kernel
        smooth=float(n*np.sum(f[1:n+1]/m))
        error=float(np.dot(f[1:n+1],kernel))
        ps=primes[primes<=n]
        prime=-float(np.sum(np.log(ps)*sums[n//ps]))
        residual=prime+smooth+error
        if abs(residual)>1e-7*(1+abs(prime)):
            raise RuntimeError(('reverse identity',n,residual))
        cohorts=[]
        for k in range(int(math.log2(n))+1):
            lo,hi=2**k,min(n+1,2**(k+1))
            cohorts.append(dict(lo=lo,hi_exclusive=hi,
                charge=int(np.sum(f[lo:hi])),
                smooth=float(n*np.sum(f[lo:hi]/np.arange(lo,hi))),
                error=float(np.dot(f[lo:hi],kernel[lo-1:hi-1])),
                charge_mean_error=float(np.mean(f[lo:hi])*np.sum(kernel[lo-1:hi-1]))))
        rows.append(dict(n=n,prime=prime,smooth=smooth,error=error,
                         residual=residual,cohorts=cohorts))
    # Linux fork shares the read-only kernels. Each worker owns one shifted sign array.
    with ProcessPoolExecutor(max_workers=8) as pool:
        control=np.array(list(pool.map(trial,range(args.seed,args.seed+args.count))))
    for j,row in enumerate(rows):
        vals=control[:,j]
        row['control_quantiles']=np.quantile(vals,[0,.05,.5,.95,1]).tolist()
        row['literal_rank']=int(np.sum(vals<row['error']))
        row['controls_smaller_abs']=int(np.sum(abs(vals)<abs(row['error'])))
        row['root']=math.sqrt(row['n'])
        print('N',row['n'],'smooth/root',row['smooth']/row['root'],
              'error/root',row['error']/row['root'],
              'rank',row['literal_rank'],'abs rank',row['controls_smaller_abs'],flush=True)
    out=dict(seconds=time.monotonic()-start,rows=rows,controls=control.tolist(),
             seeds=[args.seed,args.seed+args.count-1],power=POWER,
             intervention='independent cyclic shifts within dyadic cofactor blocks >=4')
    Path(args.output).write_text(json.dumps(out,indent=2))
    print('elapsed',out['seconds'],flush=True)
