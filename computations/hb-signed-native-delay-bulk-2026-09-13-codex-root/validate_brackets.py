#!/usr/bin/env python3
"""Medium-resolution validation and terminal intervention for discovered k brackets."""

from __future__ import annotations

import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

from native_delay import signed_action


G={1:14.134725141734695,4:30.424876125859512}
K={1:1.7802,4:1.5699}


def run(task):
    n,label,k,V=task;gamma=G[n];section={"x":-0.4,"y":-0.6,"X":0.13,"k":k,"V":V}
    hq=max(40,int(math.ceil(28+.72*gamma*V)));start=time.monotonic()
    r=signed_action(gamma,section,hq,18,24,45,40);z=r["ordered"][0]
    return {"n":n,"label":label,"k":k,"V":V,"orders":[hq,18,24],"margin":45,
            "seconds":time.monotonic()-start,"ordered_imag":float(z.imag),
            "relative":float(r["relative"][0]),"principal_imag":float(r["ordered"][1].imag),
            "tail_leverage":float(abs(z-r["ordered"][1])/max(abs(z)+abs(r["ordered"][1]),1e-300)),
            "conjugacy_error":float(abs(r["signed"][1,0]-r["signed"][0,0].conjugate())/
              max(abs(r["signed"][0,0])+abs(r["signed"][1,0]),1e-300))}


if __name__=="__main__":
    tasks=[]
    for n,ks in ((1,(1.7,K[1],1.9)),(4,(1.5,K[4],1.7))):
        tasks += [(n,"bracket",k,2.0) for k in ks]
        tasks += [(n,"terminal",K[n],V) for V in (1.5,2.5)]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p:rows=list(p.map(run,tasks))
    with open("bracket-validation.json.tmp","w") as f:json.dump(rows,f,indent=2)
    os.replace("bracket-validation.json.tmp","bracket-validation.json")
