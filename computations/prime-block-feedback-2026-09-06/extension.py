"""Sieve only the larger-scale stress-test intervals on the authorized pod."""
import argparse
import json
import math
import multiprocessing as mp
import time
from pathlib import Path

import numpy as np
from boundary import reference
from experiment import small_sieve

ROOT=Path(__file__).resolve().parent
BASE=None


def block(k):
    width=(k+1)**4-k**4
    edge_grid=k**4+(width*(8*np.arange(17)[None,:]+np.arange(8)[:,None]))//128
    low,high=int(edge_grid.min()),int(edge_grid.max())
    keep=np.ones(high-low,dtype=bool)
    for p in BASE:
        if p*p>=high:
            break
        first=max(p*p,((low+p-1)//p)*p)
        keep[first-low::p]=False
    primes=np.flatnonzero(keep)+low
    a,b=edge_grid[:,:-1].ravel(),edge_grid[:,1:].ravel()
    counts=np.searchsorted(primes,b)-np.searchsorted(primes,a)
    mass=reference(a,b,32)
    refined=reference(a,b,64)
    error=float(np.max(np.abs(mass-refined)/mass))
    assert error<1e-12
    rows=np.column_stack([np.repeat(np.arange(8),16),np.full(128,k),
        np.tile(np.arange(16),8),a,b,counts,mass])
    return rows,error


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--start",type=int,default=128)
    parser.add_argument("--stop",type=int,default=160)
    args=parser.parse_args()
    assert (args.start,args.stop) in [(128,160),(256,320)], "Only frozen scale bands are authorized here."
    suffix="" if args.start==128 else "-k256"
    start=time.monotonic()
    assert json.loads((ROOT/"boundary-validation.json").read_text())["advance"]
    if args.start==256:
        assert json.loads((ROOT/"extension.json").read_text())["advance"]
    BASE=small_sieve((args.stop+1)**2+1)
    with mp.get_context("fork").Pool(8) as pool:
        pieces=pool.map(block,range(args.start,args.stop))
    rows=np.concatenate([entry[0] for entry in pieces])
    np.savez_compressed(ROOT/f"extension{suffix}-rows.npz",rows=rows)
    results=[]
    for t in range(8):
        chosen=rows[rows[:,0]==t]
        c,L=chosen[:,5]-chosen[:,6],chosen[:,6]
        whole=c.reshape(-1,16).sum(axis=1)/np.sqrt(L.reshape(-1,16).sum(axis=1))
        fine=c/np.sqrt(L)
        results.append({"phase_eighths":t,"fine_mean_square":float(np.mean(fine*fine)),
            "whole_mean_square":float(np.mean(whole*whole)),
            "ratio":float(np.mean(whole*whole)/np.mean(fine*fine)),
            "max_whole_absolute":float(np.max(np.abs(whole))),
            "passes":bool(np.mean(whole*whole)<=.5*np.mean(fine*fine))})
    out={"candidate":"E3" if args.start==128 else "E4","range":[args.start,args.stop-1],"results":results,
        "advance":all(entry["passes"] for entry in results),
        "quadrature_max_relative_error":max(entry[1] for entry in pieces),
        "workers":8,"wall_seconds":time.monotonic()-start}
    (ROOT/f"extension{suffix}.json").write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))
