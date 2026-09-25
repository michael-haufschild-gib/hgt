"""Finite-cell attack near arithmetic endpoint coincidence; Runpod only."""
import concurrent.futures
import json
import mpmath as mp
from scan import disable_fast_sum

def finite(sigma,n,t,a,b):
    u=mp.mpc(sigma,-t)
    scale=mp.mpf(n)**(sigma+2-mp.j*t)
    cuts=[a]+[mp.mpf(j) for j in range(int(mp.floor(a))+1,int(mp.ceil(b)))]+[b]
    def cell(left,right):
        m=int(mp.floor((left+right)/2))
        def f(x):
            return (x**(1-u)/(1-u)+(2*m+1)*x**(-u)/u
                    -m*(m+1)*x**(-u-1)/(u+1))/2
        return f(right)-f(left)
    return mp.im(scale*mp.fsum(cell(left,right) for left,right in zip(cuts,cuts[1:])))

def work(params):
    sigma_text,n,ratio_text=params
    mp.mp.dps=110
    sigma,ratio=mp.mpf(sigma_text),mp.mpf(ratio_text)
    t=2*mp.pi*n*ratio
    prefixes=[]
    for k in range(1,9):
        x=n*mp.exp(2*mp.pi*k/t)
        # Avoid a huge finite-cell count at small n: the main scan covers these cutoffs.
        if x-n>3000:
            break
        prefixes.append(finite(sigma,n,t,mp.mpf(n),x))
    return dict(sigma=sigma_text,n=n,ratio=ratio_text,dps=110,
                prefixes=[mp.nstr(x,70) for x in prefixes],
                positive_prefixes=[k+1 for k,x in enumerate(prefixes) if x>0])

if __name__=='__main__':
    grid=[(s,n,r) for s in ('-1','-0.5','0','0.001','0.5','8')
          for n in (1,16,256,4096) for r in ('0.25','0.5','0.75','0.99','0.9999')]
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        rows=list(pool.map(work,grid))
    with open('boundary.json','w') as out:
        json.dump(rows,out,indent=2)
    print(json.dumps([r for r in rows if r['positive_prefixes']],indent=2))
