#!/usr/bin/env python3
"""Inverse test: find intrinsic complex-rho zeros and challenge cross-section persistence."""

from __future__ import annotations

import argparse
import cmath
import json
import math
import os
import random
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp


POINTS = [
    (2 * math.e, 0.0), (2 * math.e, 0.5), (2 * math.e, 1.0),
    (7.0, 0.17), (7.0, 0.73), (12.0, 0.37),
    (23.0, 0.11), (23.0, 0.89), (60.0, 0.5),
]


def F11(q, L, d):
    return -1/(3*q**3)+(L+d)/(4*q**4)-L*d/(5*q**5)


def F21(q, L, d):
    return -1/(3*q**3)+(2*L+d)/(4*q**4)-(L**2+2*L*d)/(5*q**5)+L**2*d/(6*q**6)


def F31(q, L, d):
    return (-1/(2*q**2)+(3*L+d)/(3*q**3)-(3*L**2+3*L*d)/(4*q**4)
            +(L**3+3*L**2*d)/(5*q**5)-L**3*d/(6*q**6))


def coeff_mp(rho, L, x, onset=True):
    L = mp.mpf(L); x = mp.mpf(x); d = (L-1)+x*L
    qp = d+1; qm = max(L, d-1)
    b11 = F11(qp,L,d)-F11(qm,L,d)
    b21 = F21(qp,L,d)-F21(qm,L,d)
    b31 = (F31(qp,L,d)-F31(qm,L,d)) if onset else 0
    delta=2*rho-1; s=rho-2; t=-rho-1
    es=(2*s+1)*(2*s+2); et=(2*t+1)*(2*t+2)
    ks=s*(s-1)/4; kt=t*(t-1)/4
    a=mp.power(L,delta)*es*(et*b11-36*kt*b21+12*kt*delta/L*b31)
    b=mp.power(L,-delta)*et*(es*b11-36*ks*b21-12*ks*delta/L*b31)
    return a-b, a, b


def zeta_zero(n):
    mp.mp.dps = 40
    return n, float(mp.im(mp.zetazero(n)))


def one_seed(task):
    idx, gamma, L, x, dr, di = task
    mp.mp.dps = 60
    z0 = mp.mpc(mp.mpf('0.5')+dr, gamma+di)
    z1 = z0 + mp.mpc('0.013', '0.019')
    try:
        root = mp.findroot(lambda z: coeff_mp(z,L,x)[0], (z0,z1), tol=mp.mpf('1e-45'), maxsteps=80)
        if not (mp.isfinite(mp.re(root)) and mp.isfinite(mp.im(root))):
            return None
        if abs(mp.re(root)) > 5 or abs(mp.im(root)) > 1000:
            return None
        local_c, a, b = coeff_mp(root,L,x)
        local_rel = abs(local_c)/max(abs(a)+abs(b),mp.mpf('1e-90'))
        residuals=[]
        for Lv,xv in POINTS:
            c,av,bv=coeff_mp(root,Lv,xv)
            residuals.append(abs(c)/max(abs(av)+abs(bv),mp.mpf('1e-90')))
        return {
            "seed_zero": idx, "seed_gamma": float(gamma), "source_L": L, "source_x": x,
            "root_re": float(mp.re(root)), "root_im": float(mp.im(root)),
            "local_relative_residual": float(local_rel),
            "validation_min": float(min(residuals)), "validation_median": float(sorted(residuals)[len(residuals)//2]),
            "validation_max": float(max(residuals)),
            "distance_to_seed_zeta": float(abs(root-mp.mpc('0.5',gamma))),
            "distance_to_self_complementary": float(abs(root-mp.mpf('0.5'))),
        }
    except Exception:
        return None


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--zeros',type=int,default=48)
    ap.add_argument('--workers',type=int,default=max(1,os.cpu_count() or 1)); ap.add_argument('--out',default='results')
    args=ap.parse_args(); os.makedirs(args.out,exist_ok=True)
    mp.mp.dps=40
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        zero_pairs=list(pool.map(zeta_zero, range(1,args.zeros+1)))
    rng=random.Random(20260913)
    tasks=[]
    source_points=[(2*math.e,0.13),(7.0,0.37),(12.0,0.71),(23.0,0.49)]
    for n,g in zero_pairs:
        for L,x in source_points:
            for _ in range(3):
                tasks.append((n,g,L,x,rng.uniform(-0.35,0.35),rng.uniform(-0.7,0.7)))
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        roots=[r for r in pool.map(one_seed,tasks,chunksize=2) if r is not None]
    # Deduplicate only for reporting; raw list retained.
    clusters={}
    for r in roots:
        key=(round(r['root_re'],8),round(r['root_im'],8))
        old=clusters.get(key)
        if old is None or r['validation_max']<old['validation_max']:
            clusters[key]=r
    unique=sorted(clusters.values(),key=lambda r:r['validation_max'])
    payload={
        "formula":"HB-TWO-SIDED-SOURCE-CURRENT equations (13)-(14)",
        "attempts":len(tasks), "converged":len(roots), "unique_roots_1e-8":len(unique),
        "persistent_below_1e-20":sum(r['validation_max']<1e-20 for r in unique),
        "persistent_below_1e-10":sum(r['validation_max']<1e-10 for r in unique),
        "best_100":unique[:100],
    }
    with open(os.path.join(args.out,'inverse_roots.json'),'w') as f: json.dump(payload,f,indent=2)
    with open(os.path.join(args.out,'inverse_roots_raw.json'),'w') as f: json.dump(roots,f)


if __name__=='__main__': main()
