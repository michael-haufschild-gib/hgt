#!/usr/bin/env python3
"""Do actual zeta ordinates align with moving source-kernel zeros beyond matched controls?"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import random
from concurrent.futures import ProcessPoolExecutor
from statistics import median

import mpmath as mp

from common import relative_residual


L_GRID=[2*math.e*(60/(2*math.e))**(j/31) for j in range(32)]
X_GRID=[j/64 for j in range(1,65)]


def zeta_zero(n):
    mp.mp.dps=40
    return n,float(mp.im(mp.zetazero(n)))


def evaluate(task):
    kind,rep,n,gamma=task
    vals=[]; best=(2.0,None,None)
    rho=complex(.5,gamma)
    for L in L_GRID:
        for x in X_GRID:
            v=relative_residual(rho,L,x)
            vals.append(v)
            if v<best[0]: best=(v,L,x)
    vals.sort()
    return {"kind":kind,"rep":rep,"n":n,"gamma":gamma,"min_rel":best[0],"min_L":best[1],"min_x":best[2],
            "q01_rel":vals[int(.01*(len(vals)-1))],"median_rel":median(vals)}


def summarize(rows):
    groups={}
    for r in rows: groups.setdefault((r['kind'],r['rep']),[]).append(r)
    out=[]
    for (kind,rep),rr in sorted(groups.items()):
        logs=[math.log10(max(r['min_rel'],1e-300)) for r in rr]
        out.append({"kind":kind,"rep":rep,"median_log10_min":median(logs),"mean_log10_min":sum(logs)/len(logs),
                    "hits_1e-4":sum(r['min_rel']<1e-4 for r in rr),"hits_1e-6":sum(r['min_rel']<1e-6 for r in rr),
                    "hits_1e-8":sum(r['min_rel']<1e-8 for r in rr),"best":min(r['min_rel'] for r in rr)})
    return out


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--zeros',type=int,default=256); ap.add_argument('--controls',type=int,default=32)
    ap.add_argument('--workers',type=int,default=max(1,os.cpu_count() or 1)); ap.add_argument('--out',default='results-height')
    args=ap.parse_args(); os.makedirs(args.out,exist_ok=True)
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        pairs=list(pool.map(zeta_zero,range(1,args.zeros+1)))
    gammas=[g for _,g in pairs]
    rng=random.Random(81238123); tasks=[]
    for n,g in pairs: tasks.append(('actual',0,n,g))
    for rep in range(1,args.controls+1):
        for i,(n,g) in enumerate(pairs):
            left=g-(gammas[i-1] if i else max(0,g-(gammas[1]-g)))
            right=(gammas[i+1] if i+1<len(gammas) else g+(g-gammas[i-1]))-g
            # Stay strictly inside the local spacing cell: matched height/density, not another known ordinate.
            jitter=rng.uniform(-.45*left,.45*right)
            tasks.append(('voronoi_jitter',rep,n,g+jitter))
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows=list(pool.map(evaluate,tasks,chunksize=2))
    with open(os.path.join(args.out,'height_rows.csv'),'w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    summaries=summarize(rows); actual=summaries[0]; controls=summaries[1:]
    payload={"zeros":args.zeros,"controls":args.controls,"grid_points_per_height":len(L_GRID)*len(X_GRID),
             "actual":actual,"controls":controls,
             "empirical_p_median_logmin":(1+sum(c['median_log10_min']<=actual['median_log10_min'] for c in controls))/(1+len(controls)),
             "empirical_p_hit_1e-6":(1+sum(c['hits_1e-6']>=actual['hits_1e-6'] for c in controls))/(1+len(controls)),
             "interpretation_direction":"Smaller log-minimum or more hits means stronger source-kernel alignment."}
    with open(os.path.join(args.out,'height_summary.json'),'w') as f: json.dump(payload,f,indent=2)


if __name__=='__main__': main()
