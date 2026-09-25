#!/usr/bin/env python3
"""Cross-section persistence challenge for selected actual zeta ordinates."""

from __future__ import annotations

import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp

from native_delay import signed_action


SECTIONS={
 "base":{"x":-0.4,"y":-0.6,"X":0.13,"k":1.5,"V":2.0},
 "direct_long":{"x":-0.8,"y":-0.3,"X":0.13,"k":1.5,"V":2.0},
 "image_short":{"x":-0.2,"y":-0.8,"X":0.13,"k":1.5,"V":2.0},
 "diagonal":{"x":-0.5,"y":-0.5,"X":0.13,"k":1.5,"V":2.0},
 "horizontal_shift":{"x":-0.4,"y":-0.6,"X":0.31,"k":1.5,"V":2.0},
 "lower_cusp":{"x":-0.4,"y":-0.6,"X":0.13,"k":0.9,"V":2.0},
 "upper_cusp":{"x":-0.4,"y":-0.6,"X":0.13,"k":2.5,"V":2.0},
 "later_terminal":{"x":-0.4,"y":-0.6,"X":0.13,"k":1.5,"V":3.0}
}


def run(task):
    n,gamma,label,section=task
    hq=max(28,int(math.ceil(20+0.60*gamma*section["V"])))
    start=time.monotonic();r=signed_action(gamma,section,hq,14,16,30,30)
    full,principal=r["ordered"]
    return {"n":n,"gamma":gamma,"label":label,"section":section,"h_order":hq,
            "seconds":time.monotonic()-start,"full_relative":float(r["relative"][0]),
            "principal_relative":float(r["relative"][1]),
            "tail_leverage":float(abs(full-principal)/max(abs(full)+abs(principal),1e-300)),
            "ordered_sign":1 if full.imag>0 else (-1 if full.imag<0 else 0),
            "normalized_ordered_abs":float(abs(full)),
            "sheet_cancellation":float(abs(r["signed"][0,0])/
              max(abs(r["direct"][0,0])+abs(r["image"][0,0]),1e-300)),
            "conjugacy_error":float(abs(r["signed"][1,0]-r["signed"][0,0].conjugate())/
              max(abs(r["signed"][0,0])+abs(r["signed"][1,0]),1e-300))}


if __name__=="__main__":
    with mp.workdps(45): pairs=[(n,float(mp.im(mp.zetazero(n)))) for n in (1,4)]
    tasks=[(n,g,label,dict(s)) for n,g in pairs for label,s in SECTIONS.items()]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p:
        rows=list(p.map(run,tasks,chunksize=1))
    with open("sections.json.tmp","w") as f:json.dump(rows,f,indent=2)
    os.replace("sections.json.tmp","sections.json")
