#!/usr/bin/env python3
"""Matched-height falsifier for cusp-base sign brackets found at zeta ordinates."""

from __future__ import annotations

import argparse
import json
import math
import os
import random
import time
from concurrent.futures import ProcessPoolExecutor

from native_delay import signed_action


def run(task):
    rep,gamma,k=task;section={"x":-0.4,"y":-0.6,"X":0.13,"k":k,"V":2.0}
    hq=max(28,int(math.ceil(20+1.2*gamma)));start=time.monotonic()
    r=signed_action(gamma,section,hq,14,16,30,30);z=r["ordered"][0]
    return {"rep":rep,"gamma":gamma,"k":k,"ordered_imag":float(z.imag),
            "relative":float(r["relative"][0]),"seconds":time.monotonic()-start}


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--group",choices=("low","high"),required=True)
    ap.add_argument("--out",required=True);args=ap.parse_args()
    # Use 45% of adjacent gaps, matching landscape controls.
    if args.group=="low": center=14.134725141734695;lo=center-.45*(21.022039638771556-center);hi=center+.45*(21.022039638771556-center);ks=(1.7,1.9)
    else: center=30.424876125859512;lo=center-.45*(center-25.01085758014569);hi=center+.45*(32.93506158773919-center);ks=(1.5,1.7)
    rng=random.Random(71093 if args.group=="low" else 71099)
    heights=[rng.uniform(lo,hi) for _ in range(8)]
    tasks=[(rep,g,k) for rep,g in enumerate(heights,1) for k in ks]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p:rows=list(p.map(run,tasks))
    crossings=[]
    for rep,g in enumerate(heights,1):
        pair=sorted((r for r in rows if r["rep"]==rep),key=lambda r:r["k"])
        crossings.append({"rep":rep,"gamma":g,"crosses":pair[0]["ordered_imag"]*pair[1]["ordered_imag"]<0})
    payload={"group":args.group,"interval":[lo,hi],"k_bracket":list(ks),"rows":rows,
             "crossings":crossings,"crossing_count":sum(r["crosses"] for r in crossings)}
    with open(args.out+".tmp","w") as f:json.dump(payload,f,indent=2)
    os.replace(args.out+".tmp",args.out)


if __name__=="__main__":main()
