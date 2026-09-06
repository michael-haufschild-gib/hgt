"""Exploratory numerical signs only. Run on the authorized Runpod, never in Lean."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import concurrent.futures
import json
import math
import platform
import time
import mpmath as mp

# Large integer cutoffs must not enter the fixed-point integer-sum accelerator.
# Use mpmath's documented-in-source direct finite-sum fallback in each process.
def disable_fast_sum(*args, **kwargs):
    raise NotImplementedError

mp.mp._zetasum_fast = disable_fast_sum


def tail(u, x):
    m = int(mp.floor(x))
    q = mp.mpf(m + 1)
    tq = (-mp.zeta(u, q + 1) - q**(1-u)/(1-u) - q**(-u)/2)/(u*(u+1))
    def primitive(y):
        return (y**(1-u)/(1-u)+(2*m+1)*y**(-u)/u
                -m*(m+1)*y**(-u-1)/(u+1))/2
    return tq + primitive(q) - primitive(x)


def work(params):
    sigma_text, n, ratio_text = params
    kmax = min(8, max(1, int(20*float(ratio_text)*n)))
    endpoint_log10 = math.log10(n) + kmax/(float(ratio_text)*n*math.log(10))
    dps = 100 + math.ceil((float(sigma_text)+3)*endpoint_log10)
    mp.mp.dps = dps
    sigma = mp.mpf(sigma_text)
    ratio = mp.mpf(ratio_text)
    t = 2*mp.pi*n*ratio
    s = mp.mpc(sigma, t)
    u = mp.conj(s)
    scale = mp.mpf(n)**(2*sigma+2-s)
    values = []
    for k in range(kmax+1):
        x = mp.mpf(n)*mp.exp(2*mp.pi*k/t)
        values.append(scale*tail(u, x))
    blocks = [mp.im(values[k]-values[k+1]) for k in range(kmax)]
    prefixes = [mp.im(values[0]-values[k]) for k in range(1, kmax+1)]
    return dict(sigma=sigma_text, n=n, ratio=ratio_text, kmax=kmax, dps=dps,
                whole_tail=mp.nstr(mp.im(values[0]), 60),
                blocks=[mp.nstr(x, 60) for x in blocks],
                prefixes=[mp.nstr(x, 60) for x in prefixes],
                positive_blocks=[k for k,x in enumerate(blocks) if x>0],
                positive_prefixes=[k+1 for k,x in enumerate(prefixes) if x>0])


if __name__ == '__main__':
    started = time.time()
    grid = [(sigma,n,ratio) for sigma in ('0.05','0.5','2','8')
            for n in (1,4,16,64) for ratio in ('0.3','0.7','0.95','0.9999')]
    rows = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        for row in pool.map(work,grid):
            rows.append(row)
            print(json.dumps({k:row[k] for k in ('sigma','n','ratio','positive_blocks','positive_prefixes')}),flush=True)
    result = dict(python=platform.python_version(), mpmath=mp.__version__,
                  workers=8, elapsed_seconds=time.time()-started,
                  normalization='n^(2*sigma+2), positive real factor', rows=rows)
    with open('results.json','w') as out:
        json.dump(result,out,indent=2)
