"""Runpod-only cosine-endpoint layer test, independent of the Hurwitz evaluator."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[key]='1'
import concurrent.futures
import json
import mpmath as mp

def layer(n,ratio,delta,k):
    t=2*mp.pi*n*ratio
    top=n*mp.exp(k/(n*ratio))
    if top-n>3000:
        return None
    terms=[]
    for m in range(n,int(mp.ceil(top))):
        left=mp.mpf(m)+delta
        right=min(mp.mpf(m)+1-delta,top)
        if left<right:
            terms.append((mp.cos(t*mp.log(left/n))-mp.cos(t*mp.log(right/n)))/t)
    return mp.fsum(terms)

def work(params):
    n,r_text,d_text,k=params
    mp.mp.dps=100
    r,d=mp.mpf(r_text),mp.mpf(d_text)
    value=layer(n,r,d,k)
    return dict(n=n,ratio=r_text,delta=d_text,k=k,skipped=value is None,
                value=None if value is None else mp.nstr(value,80),
                negative=False if value is None else bool(value < -mp.mpf('1e-70')))

if __name__=='__main__':
    grid=[(n,r,d,k) for n in (1,4,16,128)
          for r in ('0.25','0.5','0.75','0.99')
          for d in ('0','0.05','0.25','0.45','0.499') for k in (1,2,4,8)]
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        rows=list(pool.map(work,grid))
    with open('layers.json','w') as out:
        json.dump(rows,out,indent=2)
    print(json.dumps([x for x in rows if x['negative']],indent=2),flush=True)
