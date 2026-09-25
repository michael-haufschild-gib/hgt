#!/usr/bin/env python3
"""Reverse test: complex roots of signed complementary direct period contact."""

from __future__ import annotations

import argparse,json,math,os,random
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp
from contact_common import direct_period_integral


def zeta_zero(n):
    mp.mp.dps=35;return n,float(mp.im(mp.zetazero(n)))


def signed(delta,V=4,order=64):
    a=direct_period_integral(delta,V,order);b=direct_period_integral(-delta,V,order)
    return a-b,a,b


def solve(task):
    n,g,dr,di=task
    z0=complex(dr,2*g+di);z1=z0+complex(.017,.031)
    try:
        for _ in range(50):
            f0,_,_=signed(z0);f1,a,b=signed(z1)
            scale=max(abs(a)+abs(b),1e-200)
            if abs(f1)/scale<1e-10:break
            if f1==f0:return None
            z2=z1-f1*(z1-z0)/(f1-f0);z0,z1=z1,z2
            if abs(z1.real)>10 or abs(z1.imag)>1000:return None
        f,a,b=signed(z1);local=abs(f)/max(abs(a)+abs(b),1e-200)
        if local>=1e-8:return None
        vals=[]
        for V in [2.,4.,8.]:
            fv,av,bv=signed(z1,V,128);vals.append(abs(fv)/max(abs(av)+abs(bv),1e-200))
        return {"seed_n":n,"seed_gamma":g,"delta_re":z1.real,"delta_im":z1.imag,
                "rho_re":(z1.real+1)/2,"rho_im":z1.imag/2,"local_rel":local,
                "validation_V2":vals[0],"validation_V4":vals[1],"validation_V8":vals[2],
                "validation_max":max(vals)}
    except Exception:return None


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--zeros',type=int,default=32);ap.add_argument('--workers',type=int,default=16)
    ap.add_argument('--out',default='roots.json');args=ap.parse_args()
    with ProcessPoolExecutor(max_workers=args.workers) as p:pairs=list(p.map(zeta_zero,range(1,args.zeros+1)))
    rng=random.Random(77129);tasks=[]
    for n,g in pairs:
        for _ in range(8):tasks.append((n,g,rng.uniform(-1.5,1.5),rng.uniform(-3,3)))
    with ProcessPoolExecutor(max_workers=args.workers) as p:raw=[r for r in p.map(solve,tasks,chunksize=1) if r]
    uniq={}
    for r in raw:
        k=(round(r['delta_re'],7),round(r['delta_im'],7))
        if k not in uniq or r['validation_max']<uniq[k]['validation_max']:uniq[k]=r
    roots=sorted(uniq.values(),key=lambda r:r['validation_max'])
    payload={"attempts":len(tasks),"converged":len(raw),"unique":len(roots),
             "persistent_1e-6":int(sum(r['validation_max']<1e-6 for r in roots)),"roots":roots}
    tmp=args.out+'.tmp'
    with open(tmp,'w') as f:
        json.dump(payload,f,indent=2)
    os.replace(tmp,args.out)


if __name__=='__main__':main()
