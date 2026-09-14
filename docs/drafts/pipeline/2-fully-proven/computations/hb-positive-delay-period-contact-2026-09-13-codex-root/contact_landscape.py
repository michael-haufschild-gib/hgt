#!/usr/bin/env python3
"""Actual-zero/matched-height landscape for signed direct period contact."""

from __future__ import annotations

import argparse,csv,json,math,os,random
from concurrent.futures import ProcessPoolExecutor
from statistics import median
import mpmath as mp

from contact_common import direct_period_integral


def zeta_zero(n):
    mp.mp.dps=40; return n,float(mp.im(mp.zetazero(n)))


def evaluate(task):
    kind,rep,n,gamma,V,order=task
    delta=complex(0,2*gamma)
    a=direct_period_integral(delta,V,order)
    b=direct_period_integral(-delta,V,order)
    signed=a-b
    return {"kind":kind,"rep":int(rep),"n":int(n),"gamma":float(gamma),"V":float(V),"order":int(order),
            "a_re":float(a.real),"a_im":float(a.imag),"b_re":float(b.real),"b_im":float(b.imag),
            "signed_abs":float(abs(signed)),"relative_signed":float(abs(signed)/max(abs(a)+abs(b),1e-300)),
            "conjugacy_error":float(abs(b-a.conjugate())/max(abs(a)+abs(b),1e-300))}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--zeros',type=int,default=64); ap.add_argument('--controls',type=int,default=8)
    ap.add_argument('--order',type=int,default=48); ap.add_argument('--refine-order',type=int,default=80)
    ap.add_argument('--workers',type=int,default=max(1,os.cpu_count() or 1)); ap.add_argument('--out',default='results')
    args=ap.parse_args(); os.makedirs(args.out,exist_ok=True)
    with ProcessPoolExecutor(max_workers=args.workers) as pool: pairs=list(pool.map(zeta_zero,range(1,args.zeros+1)))
    gs=[g for _,g in pairs]; rng=random.Random(551903); tasks=[]
    for n,g in pairs:
        for V in [2.0,4.0,8.0]: tasks.append(('actual',0,n,g,V,args.order))
        tasks.append(('actual_refined',0,n,g,4.0,args.refine_order))
    for rep in range(1,args.controls+1):
        for i,(n,g) in enumerate(pairs):
            left=g-(gs[i-1] if i else max(0,g-(gs[1]-g))); right=(gs[i+1] if i+1<len(gs) else g+(g-gs[i-1]))-g
            tasks.append(('jitter',rep,n,g+rng.uniform(-.45*left,.45*right),4.0,args.order))
    with ProcessPoolExecutor(max_workers=args.workers) as pool: rows=list(pool.map(evaluate,tasks,chunksize=1))
    with open(os.path.join(args.out,'contact_rows.csv'),'w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    actual=[r for r in rows if r['kind']=='actual' and r['V']==4]
    refined=[r for r in rows if r['kind']=='actual_refined']
    by={(r['n']):r for r in refined}
    refine=max(abs(r['relative_signed']-by[r['n']]['relative_signed']) for r in actual)
    controls=[]
    for rep in range(1,args.controls+1):
        rr=[r for r in rows if r['kind']=='jitter' and r['rep']==rep]
        controls.append({"rep":rep,"median_relative":median(r['relative_signed'] for r in rr),
                         "min_relative":min(r['relative_signed'] for r in rr),
                         "hits_1e-6":sum(r['relative_signed']<1e-6 for r in rr)})
    act={"median_relative":median(r['relative_signed'] for r in actual),"min_relative":min(r['relative_signed'] for r in actual),
         "hits_1e-6":sum(r['relative_signed']<1e-6 for r in actual)}
    payload={"zeros":args.zeros,"V_primary":4,"actual":act,"controls":controls,
             "empirical_p_median":(1+sum(c['median_relative']<=act['median_relative'] for c in controls))/(1+len(controls)),
             "max_absolute_refinement_change":refine,
             "max_conjugacy_error":max(r['conjugacy_error'] for r in rows),
             "V_medians":{str(V):median(r['relative_signed'] for r in rows if r['kind']=='actual' and r['V']==V) for V in [2.,4.,8.]}}
    with open(os.path.join(args.out,'summary.json'),'w') as f:json.dump(payload,f,indent=2)


if __name__=='__main__':main()
