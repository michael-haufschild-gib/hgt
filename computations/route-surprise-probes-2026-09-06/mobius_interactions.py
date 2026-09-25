"""Where later source blocks reinforce or compensate a given block."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from scipy.special import gamma
from scipy.integrate import quad
import mpmath as mp
from mobius_blocks import source, integer_convolution


def run(spec):
    kind,seed = spec
    mu = source(kind,seed,2**18)
    blocks = [(1,16)]+[(2**k+1,2**(k+1)) for k in range(4,18)]
    r = 1.01
    gram = np.zeros((len(blocks),len(blocks)))
    max_error = 0
    for i,(a,b) in enumerate(blocks):
        for j in range(i,len(blocks)):
            c,d = blocks[j]
            conv,err = integer_convolution(mu[a:b+1],mu[c:d+1])
            max_error = max(max_error,err)
            k = np.arange(len(conv),dtype=np.longdouble)+a+c
            val = gamma(r)*np.sum(conv*k**(-r),dtype=np.longdouble)
            gram[i,j] = gram[j,i] = float(val)
    diagonal = np.diag(gram)
    corr = gram/np.sqrt(diagonal[:,None]*diagonal[None,:])
    future = np.zeros_like(gram)
    for i in range(len(blocks)):
        future[i,i+1:] = -2*np.cumsum(gram[i,i+1:])/gram[i,i]
    return dict(kind=kind,seed=seed,r=r,blocks=blocks,gram=gram.tolist(),
        correlation=corr.tolist(),future_repayment=future.tolist(),
        block_sums=[int(sum(mu[a:b+1])) for a,b in blocks],
        fft_rounding_error=max_error)


def witness():
    n = 256
    mu = source("literal",0,2**18)[:2*n+1]
    mp.mp.dps = 80
    rows = []
    # Independent integer loops, no FFT in this calculation.
    coefficients = [0]*(3*n+1)
    for m in range(1,n+1):
        for j in range(n+1,2*n+1):
            coefficients[m+j] += int(mu[m])*int(mu[j])
    ma = np.arange(1,n+1)
    mb = np.arange(n+1,2*n+1)
    for rs in ("1.01","1.5"):
        r = mp.mpf(rs)
        direct = mp.gamma(r)*sum(mp.mpf(c)/mp.mpf(k)**r for k,c in enumerate(coefficients) if c)
        def integrand(x):
            return x**(float(r)-1)*np.dot(mu[1:n+1],np.exp(-ma*x))*np.dot(mu[n+1:],np.exp(-mb*x))
        split = [0,1e-5,.001,.01,.1,1,10,50]
        integral = error = 0.
        for a,b in zip(split[:-1],split[1:]):
            v,e = quad(integrand,a,b,epsabs=1e-13,epsrel=1e-12,limit=150)
            integral += v
            error += e
        rows.append(dict(N=n,r=rs,direct_80dps=mp.nstr(direct,65),
            laplace_quadrature=integral,quadrature_estimated_error=error,
            difference=float(mp.mpf(integral)-direct)))
    return rows


if __name__ == "__main__":
    start = time.monotonic()
    specs = [("literal",0)]+[(kind,seed) for kind in ("shell_shuffle","random_multiplicative") for seed in (101,202,303,404)]
    with ProcessPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run,specs))
    out = dict(seconds=time.monotonic()-start,results=results,validation=witness())
    with open("mobius-interactions.json","w") as f:
        json.dump(out,f,indent=2)
    literal = results[0]
    for i,block in enumerate(literal["blocks"]):
        if i+3 < len(literal["blocks"]):
            print(block,"energy",literal["gram"][i][i],"future3_repayment",
                literal["future_repayment"][i][i+3],"all_available",literal["future_repayment"][i][-1],flush=True)
    print("validation",out["validation"],flush=True)
    print("seconds",time.monotonic()-start,flush=True)
