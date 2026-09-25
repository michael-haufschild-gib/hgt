#!/usr/bin/env python3
"""Fixed-section spectral scan for non-arithmetic signed-delay root intervals."""

from __future__ import annotations

import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

from native_delay import signed_action


SECTION={"x":-0.4,"y":-0.6,"X":0.13,"k":1.5,"V":2.0}


def run(gamma):
    hq=max(28,int(math.ceil(20+1.2*gamma)));start=time.monotonic()
    r=signed_action(gamma,SECTION,hq,14,16,30,30);z=r["ordered"][0]
    return {"gamma":gamma,"h_order":hq,"seconds":time.monotonic()-start,
            "ordered_imag":float(z.imag),"relative":float(r["relative"][0]),
            "principal_imag":float(r["ordered"][1].imag),
            "tail_leverage":float(abs(z-r["ordered"][1])/max(abs(z)+abs(r["ordered"][1]),1e-300)),
            "conjugacy_error":float(abs(r["signed"][1,0]-r["signed"][0,0].conjugate())/
              max(abs(r["signed"][0,0])+abs(r["signed"][1,0]),1e-300))}


if __name__=="__main__":
    heights=[10+2.5*j for j in range(15)]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p:rows=list(p.map(run,heights))
    brackets=[]
    for a,b in zip(rows,rows[1:]):
        if a["ordered_imag"]*b["ordered_imag"]<0:brackets.append([a["gamma"],b["gamma"]])
    payload={"section":SECTION,"rows":rows,"sign_change_brackets":brackets}
    with open("height-scan.json.tmp","w") as f:json.dump(payload,f,indent=2)
    os.replace("height-scan.json.tmp","height-scan.json")
