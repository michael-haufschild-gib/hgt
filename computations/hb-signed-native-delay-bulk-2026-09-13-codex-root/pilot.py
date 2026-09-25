#!/usr/bin/env python3
"""Cost and crossed-resolution pilot for one literal signed-delay section."""

from __future__ import annotations

import json
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp

from native_delay import signed_action


SECTION={"x":-0.4,"y":-0.6,"X":0.13,"k":1.5,"V":2.0}


def run(task):
    n,hq,cq,tq,margin,dps=task
    with mp.workdps(45): gamma=float(mp.im(mp.zetazero(n)))
    start=time.monotonic()
    result=signed_action(gamma,SECTION,hq,cq,tq,margin,dps)
    def pair(z): return [float(z.real),float(z.imag)]
    return {"n":n,"gamma":gamma,"h_order":hq,"clock_order":cq,"theta_order":tq,
            "margin":margin,"dps":dps,"seconds":time.monotonic()-start,
            "full_relative":float(result["relative"][0]),
            "principal_relative":float(result["relative"][1]),
            "full_ordered":pair(result["ordered"][0]),
            "principal_ordered":pair(result["ordered"][1]),
            "full_sheet":pair(result["signed"][0,0]),
            "full_conjugacy_error":float(abs(result["signed"][1,0]-result["signed"][0,0].conjugate())/
                                           max(abs(result["signed"][0,0])+abs(result["signed"][1,0]),1e-300)),
            "log_abs_completed_lambda_sq":result["log_abs_completed_lambda_sq"]}


if __name__=="__main__":
    configs=[(1,28,12,16,30,30),(1,40,16,24,40,35),(1,52,20,32,50,45),
             (4,56,14,16,30,30),(4,72,18,24,40,35)]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p:
        rows=list(p.map(run,configs,chunksize=1))
    with open("pilot.json.tmp","w") as f:json.dump(rows,f,indent=2)
    os.replace("pilot.json.tmp","pilot.json")
