#!/usr/bin/env python3
"""Cusp-base scan for geometry-tuned zeros of literal signed delay sector."""

from __future__ import annotations

import argparse
import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

from native_delay import signed_action


GAMMAS={"zeta1":14.134725141734695,"control1":15.209498330211435,
        "zeta4":30.424876125859512,"control4":31.1828776617478}


def run(task):
    label,gamma,k=task;section={"x":-0.4,"y":-0.6,"X":0.13,"k":k,"V":2.0}
    hq=max(28,int(math.ceil(20+1.2*gamma)));start=time.monotonic()
    r=signed_action(gamma,section,hq,14,16,30,30);z=r["ordered"][0]
    return {"label":label,"gamma":gamma,"k":k,"h_order":hq,"seconds":time.monotonic()-start,
            "ordered_imag":float(z.imag),"relative":float(r["relative"][0]),
            "normalized_abs":float(abs(z)),"conjugacy_error":float(abs(r["signed"][1,0]-r["signed"][0,0].conjugate())/
              max(abs(r["signed"][0,0])+abs(r["signed"][1,0]),1e-300))}


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--group",choices=("low","high"),required=True)
    ap.add_argument("--out",required=True);args=ap.parse_args()
    labels=("zeta1","control1") if args.group=="low" else ("zeta4","control4")
    tasks=[(label,GAMMAS[label],k) for label in labels for k in (1.5,1.7,1.9,2.1,2.3,2.5)]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p:rows=list(p.map(run,tasks))
    with open(args.out+".tmp","w") as f:json.dump(rows,f,indent=2)
    os.replace(args.out+".tmp",args.out)


if __name__=="__main__":main()
