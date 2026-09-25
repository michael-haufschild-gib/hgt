#!/usr/bin/env python3
"""Hostile broad-seed search for off-critical intrinsic roots."""

from __future__ import annotations

import argparse
import json
import os
import random
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp

from inverse_roots import POINTS, coeff_mp


SOURCE_POINTS = [(2*mp.e, mp.mpf('0.13')), (7, mp.mpf('0.37')),
                 (12, mp.mpf('0.71')), (23, mp.mpf('0.49'))]


def solve(task):
    L, x, sr, si, step_r, step_i = task
    mp.mp.dps = 70
    z0 = mp.mpc(sr, si); z1 = z0 + mp.mpc(step_r, step_i)
    try:
        root = mp.findroot(lambda z: coeff_mp(z,L,x)[0], (z0,z1), tol=mp.mpf('1e-50'), maxsteps=100)
        if not (mp.isfinite(mp.re(root)) and mp.isfinite(mp.im(root))): return None
        if abs(mp.re(root)) > 10 or abs(mp.im(root)) > 500: return None
        c,a,b=coeff_mp(root,L,x)
        lr=abs(c)/max(abs(a)+abs(b),mp.mpf('1e-100'))
        vals=[]
        for Lv,xv in POINTS:
            cv,av,bv=coeff_mp(root,Lv,xv)
            vals.append(abs(cv)/max(abs(av)+abs(bv),mp.mpf('1e-100')))
        return {"L":float(L),"x":float(x),"root_re":float(mp.re(root)),"root_im":float(mp.im(root)),
                "local_rel":float(lr),"validation_max":float(max(vals)),
                "critical_distance":float(abs(mp.re(root)-mp.mpf('0.5')))}
    except Exception:
        return None


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--attempts',type=int,default=4096)
    ap.add_argument('--workers',type=int,default=max(1,os.cpu_count() or 1)); ap.add_argument('--out',default='results-broad')
    args=ap.parse_args(); os.makedirs(args.out,exist_ok=True)
    rng=random.Random(9071984); tasks=[]
    for i in range(args.attempts):
        L,x=SOURCE_POINTS[i%len(SOURCE_POINTS)]
        tasks.append((L,x,rng.uniform(-2,3),rng.uniform(-250,250),rng.uniform(-.2,.2),rng.uniform(-.2,.2)))
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        raw=[r for r in pool.map(solve,tasks,chunksize=4) if r]
    uniq={}
    for r in raw:
        key=(round(r['root_re'],9),round(r['root_im'],9),r['L'],r['x'])
        if key not in uniq or r['local_rel']<uniq[key]['local_rel']: uniq[key]=r
    roots=list(uniq.values())
    off=[r for r in roots if r['critical_distance']>1e-20]
    persistent=[r for r in roots if r['validation_max']<1e-20]
    payload={"attempts":len(tasks),"converged":len(raw),"unique_by_point":len(roots),
             "critical_line":len(roots)-len(off),"off_critical":len(off),
             "persistent_all_points_1e-20":len(persistent),
             "max_critical_distance_among_near_line":max([r['critical_distance'] for r in roots if r['critical_distance']<=1e-20] or [0]),
             "off_critical_roots":sorted(off,key=lambda r:r['critical_distance'],reverse=True)[:200],
             "persistent_roots":persistent[:200]}
    with open(os.path.join(args.out,'broad_roots.json'),'w') as f: json.dump(payload,f,indent=2)
    with open(os.path.join(args.out,'broad_roots_raw.json'),'w') as f: json.dump(raw,f)


if __name__=='__main__': main()
