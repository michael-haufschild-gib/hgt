#!/usr/bin/env python3
"""High-resolution challenges for strongest/surprising signed-delay cases."""

from __future__ import annotations

import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp

from native_delay import signed_action


CASES=[
 (4,"base",{"x":-0.4,"y":-0.6,"X":0.13,"k":1.5,"V":2.0}),
 (4,"image_short",{"x":-0.2,"y":-0.8,"X":0.13,"k":1.5,"V":2.0}),
 (3,"base",{"x":-0.4,"y":-0.6,"X":0.13,"k":1.5,"V":2.0}),
 (1,"upper_cusp",{"x":-0.4,"y":-0.6,"X":0.13,"k":2.5,"V":2.0})]


def run(task):
    n,label,section,level=task
    with mp.workdps(50):gamma=float(mp.im(mp.zetazero(n)))
    if level=="medium": hq,cq,tq,margin,dps=(max(40,int(math.ceil(28+.72*gamma*section["V"]))),18,24,45,40)
    else: hq,cq,tq,margin,dps=(max(52,int(math.ceil(36+.82*gamma*section["V"]))),22,32,60,50)
    start=time.monotonic();r=signed_action(gamma,section,hq,cq,tq,margin,dps)
    full,principal=r["ordered"]
    return {"n":n,"label":label,"level":level,"section":section,"gamma":gamma,
            "orders":[hq,cq,tq],"margin":margin,"dps":dps,"seconds":time.monotonic()-start,
            "full_relative":float(r["relative"][0]),"principal_relative":float(r["relative"][1]),
            "ordered_imag":float(full.imag),"principal_imag":float(principal.imag),
            "tail_leverage":float(abs(full-principal)/max(abs(full)+abs(principal),1e-300)),
            "sheet_cancellation":float(abs(r["signed"][0,0])/
              max(abs(r["direct"][0,0])+abs(r["image"][0,0]),1e-300)),
            "conjugacy_error":float(abs(r["signed"][1,0]-r["signed"][0,0].conjugate())/
              max(abs(r["signed"][0,0])+abs(r["signed"][1,0]),1e-300))}


if __name__=="__main__":
    tasks=[(*case,level) for case in CASES for level in ("medium","high")]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p:rows=list(p.map(run,tasks))
    with open("refined.json.tmp","w") as f:json.dump(rows,f,indent=2)
    os.replace("refined.json.tmp","refined.json")
