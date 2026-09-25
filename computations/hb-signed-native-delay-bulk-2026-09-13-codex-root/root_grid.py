#!/usr/bin/env python3
"""Parallel refinement grid for one fixed-section non-zeta action root."""

from __future__ import annotations

import argparse
import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

from native_delay import signed_action


SECTION={"x":-0.4,"y":-0.6,"X":0.13,"k":1.5,"V":2.0}


def run(gamma):
    hq=max(36,int(math.ceil(24+1.35*gamma)));start=time.monotonic()
    r=signed_action(gamma,SECTION,hq,16,20,38,35);z=r["ordered"][0]
    return {"gamma":gamma,"ordered_imag":float(z.imag),"relative":float(r["relative"][0]),
            "h_order":hq,"seconds":time.monotonic()-start,"conjugacy_error":float(abs(r["signed"][1,0]-r["signed"][0,0].conjugate())/
              max(abs(r["signed"][0,0])+abs(r["signed"][1,0]),1e-300))}


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--lo",type=float,required=True);ap.add_argument("--hi",type=float,required=True)
    ap.add_argument("--points",type=int,default=9);ap.add_argument("--out",required=True);args=ap.parse_args()
    heights=[args.lo+(args.hi-args.lo)*j/(args.points-1) for j in range(args.points)]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p:rows=list(p.map(run,heights))
    brackets=[]
    for a,b in zip(rows,rows[1:]):
        if a["ordered_imag"]*b["ordered_imag"]<0:brackets.append([a["gamma"],b["gamma"]])
    payload={"section":SECTION,"rows":rows,"sign_change_brackets":brackets}
    with open(args.out+".tmp","w") as f:json.dump(payload,f,indent=2)
    os.replace(args.out+".tmp",args.out)


if __name__=="__main__":main()
