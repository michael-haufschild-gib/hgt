#!/usr/bin/env python3
"""Crossed quadrature refinement for selected actual and control heights."""

from concurrent.futures import ProcessPoolExecutor
import json,os
from contact_common import direct_period_integral

CASES=[14.134725141734695,87.42527461312523,111.02953554316967,
       167.1844399781745,169.9119764794117,170.314]

def run(task):
    g,order,V=task;d=2j*g
    a=direct_period_integral(d,V,order);b=direct_period_integral(-d,V,order)
    return {"gamma":g,"order":order,"V":V,"a_re":float(a.real),"a_im":float(a.imag),
            "relative_signed":float(abs(a-b)/(abs(a)+abs(b))),
            "conjugacy_error":float(abs(b-a.conjugate())/(abs(a)+abs(b)))}

if __name__=='__main__':
    tasks=[(g,o,V) for g in CASES for V in [2.,4.,8.] for o in [48,80,128,192]]
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as p: rows=list(p.map(run,tasks))
    json.dump(rows,open('refinement.json','w'),indent=2)
