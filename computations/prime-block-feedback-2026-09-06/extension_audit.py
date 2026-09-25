"""Independent high-precision reference-mass audit, authorized pod only."""
import json
import multiprocessing as workers
import time
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT=Path(__file__).resolve().parent
ROWS=None


def check(t):
    mp.mp.dps=60
    rows=ROWS[ROWS[:,0]==t]
    masses=[mp.ei(mp.log(int(r[4])))-mp.ei(mp.log(int(r[3]))) for r in rows]
    c=[mp.mpf(int(r[5]))-L for r,L in zip(rows,masses)]
    fine=mp.fsum(v*v/L for v,L in zip(c,masses))/len(c)
    whole=mp.fsum(mp.fsum(c[i:i+16])**2/mp.fsum(masses[i:i+16])
                  for i in range(0,len(c),16))/(len(c)//16)
    return {"phase_eighths":t,"digits":60,"fine_mean_square":mp.nstr(fine,50),
            "whole_mean_square":mp.nstr(whole,50),"ratio":mp.nstr(whole/fine,50),
            "threshold_gap":mp.nstr(whole/fine-mp.mpf('.5'),50),
            "passes":bool(whole/fine<=mp.mpf('.5'))}


if __name__=="__main__":
    start=time.monotonic()
    ROWS=np.load(ROOT/"extension-k256-rows.npz")["rows"]
    with workers.get_context("fork").Pool(8) as pool:
        results=pool.map(check,range(8))
    ordinary=json.loads((ROOT/"extension-k256.json").read_text())
    for a,b in zip(results,ordinary["results"]):
        assert abs(float(a["ratio"])-b["ratio"])<1e-9
        assert a["passes"]==b["passes"]
    out={"candidate":"E4","reference_audit":"60-digit Ei antiderivative in every cell",
         "results":results,"wall_seconds":time.monotonic()-start}
    (ROOT/"extension-audit.json").write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))
