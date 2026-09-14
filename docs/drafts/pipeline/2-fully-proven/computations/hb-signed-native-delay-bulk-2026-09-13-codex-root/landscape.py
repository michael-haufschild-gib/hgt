#!/usr/bin/env python3
"""Actual-zero and locally matched-control landscape for literal signed delay action."""

from __future__ import annotations

import argparse
import json
import math
import os
import random
import time
from concurrent.futures import ProcessPoolExecutor
from statistics import median

import mpmath as mp

from native_delay import signed_action


SECTION={"x":-0.4,"y":-0.6,"X":0.13,"k":1.5,"V":2.0}


def zeta_pair(n):
    with mp.workdps(45): return n,float(mp.im(mp.zetazero(n)))


def encode(task):
    kind,n,gamma,section=task
    hq=max(28,int(math.ceil(20+0.60*gamma*section["V"])))
    start=time.monotonic()
    r=signed_action(gamma,section,hq,14,16,30,30)
    full,principal=r["ordered"]
    signed_full=r["signed"][0,0]
    direct_full,image_full=r["direct"][0,0],r["image"][0,0]
    physical_logabs=(math.log(max(abs(full),1e-300))+r["log_abs_completed_lambda_sq"])
    return {"kind":kind,"n":int(n),"gamma":float(gamma),"section":section,
            "h_order":hq,"seconds":time.monotonic()-start,
            "full_relative":float(r["relative"][0]),
            "principal_relative":float(r["relative"][1]),
            "tail_leverage":float(abs(full-principal)/max(abs(full)+abs(principal),1e-300)),
            "sheet_cancellation":float(abs(signed_full)/max(abs(direct_full)+abs(image_full),1e-300)),
            "direct_relative":float(abs(r["direct_ordered"][0])/max(abs(r["direct"][0,0])+abs(r["direct"][1,0]),1e-300)),
            "image_relative":float(abs(r["image_ordered"][0])/max(abs(r["image"][0,0])+abs(r["image"][1,0]),1e-300)),
            "ordered_sign":1 if full.imag>0 else (-1 if full.imag<0 else 0),
            "normalized_ordered_abs":float(abs(full)),
            "physical_ordered_logabs":float(physical_logabs),
            "conjugacy_error":float(abs(r["signed"][1,0]-r["signed"][0,0].conjugate())/
                                      max(abs(r["signed"][0,0])+abs(r["signed"][1,0]),1e-300))}


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--zeros",type=int,default=8)
    ap.add_argument("--workers",type=int,default=16);ap.add_argument("--out",default="landscape.json")
    args=ap.parse_args()
    with ProcessPoolExecutor(max_workers=args.workers) as p:
        pairs=list(p.map(zeta_pair,range(1,args.zeros+1)))
    gs=[g for _,g in pairs];rng=random.Random(420771);tasks=[]
    for i,(n,g) in enumerate(pairs):
        tasks.append(("actual",n,g,dict(SECTION)))
        left=g-(gs[i-1] if i else max(0,g-(gs[1]-g)))
        right=(gs[i+1] if i+1<len(gs) else g+(g-gs[i-1]))-g
        tasks.append(("control",n,g+rng.uniform(-.45*left,.45*right),dict(SECTION)))
    with ProcessPoolExecutor(max_workers=args.workers) as p:
        rows=list(p.map(encode,tasks,chunksize=1))
    summary={}
    for kind in ("actual","control"):
        rr=[r for r in rows if r["kind"]==kind]
        summary[kind]={key:median(r[key] for r in rr) for key in
                       ("full_relative","principal_relative","tail_leverage","sheet_cancellation")}
    payload={"rows":rows,"median":summary}
    with open(args.out+".tmp","w") as f:json.dump(payload,f,indent=2)
    os.replace(args.out+".tmp",args.out)


if __name__=="__main__":main()
