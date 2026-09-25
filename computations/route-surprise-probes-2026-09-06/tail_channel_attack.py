"""Hostile multi-atom test of the derived two-channel budget candidate."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
import random
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp
from tail_interventions import data_with_jets, atomic_jets
from tail_moment_dissection import channels
import clg_compensation as old


def run(seed):
    mp.mp.dps = 80
    rng = random.Random(seed)
    rows = []
    invalid = 0
    for index in range(256):
        a0 = mp.pi + mp.mpf(rng.random())*20
        t = mp.mpf(10)**mp.mpf(-6+6.3*rng.random())
        x0 = mp.log(a0/mp.pi)/2
        u = x0+t
        if mp.pi*mp.exp(2*u)<6:
            invalid += 1
            continue
        mass = old.moments(old.Bcoord(x0))[0]-1
        gs = [mp.mpf(3)] + [mp.mpf(3)*mp.mpf(10)**mp.mpf(5*rng.random()) for _ in range(3)]
        ps = [mp.mpf(1)] + [mp.mpf(10)**mp.mpf(-24+24*rng.random()) for _ in range(3)]
        ps = [v/sum(ps) for v in ps]
        d = data_with_jets(u,t,lambda x:atomic_jets(x,x0,mass,gs,ps))
        lmax = min(mp.mpf(1),mp.mpf(".99")*d["q"]/(-d["dq"])) if d["dq"]<0 else mp.mpf(1)
        for l in (mp.mpf(0),lmax/2,lmax):
            terms,h2 = channels(d,l)
            value = sum(terms)
            a,b,s,m = [d[v]+l*d["d"+v] for v in ("a","b","s","m")]
            h = a*t*m-(a+t*b)*s
            h1 = d["da"]*t*m+a*t*d["dm"]-(d["da"]+t*d["db"])*s-(a+t*b)*d["ds"]
            firsttwo = terms[0]+terms[1]
            w1 = -terms[2]/(3*h2) if h2 else mp.mpf(0)
            scale = sum(abs(v) for v in terms)
            rows.append(dict(seed=seed,index=index,left_A=mp.nstr(a0,30),t=mp.nstr(t,30),l=mp.nstr(l,30),
                nodes=[mp.nstr(g,30) for g in gs],probs=[mp.nstr(p,30) for p in ps],
                mass=mp.nstr(mass,30),firsttwo=mp.nstr(firsttwo,30),w1=mp.nstr(w1,30),
                h2=mp.nstr(h2,30),h=mp.nstr(h,30),h1=mp.nstr(h1,30),
                c3=mp.nstr(value,30),normalized_firsttwo=mp.nstr(firsttwo/scale,20),
                positive_action=True,positive_a=a>0,positive_b=b>0,positive_s=s>0,
                channels=[mp.nstr(v,30) for v in terms]))
    return dict(seed=seed,invalid_structural=invalid,rows=rows)


if __name__ == "__main__":
    start = time.monotonic()
    with ProcessPoolExecutor(max_workers=8) as pool:
        groups = list(pool.map(run,range(901,909)))
    rows = [r for group in groups for r in group["rows"]]
    bad = [r for r in rows if mp.mpf(r["firsttwo"])<0 or mp.mpf(r["w1"])>0]
    tight = [r for r in bad if r["positive_a"] and r["positive_b"] and r["positive_s"]
        and mp.mpf(r["h"])<0 and mp.mpf(r["h1"])>0 and mp.mpf(r["h2"])>0]
    out = dict(seconds=time.monotonic()-start,results=groups)
    with open("tail-channel-attack.json","w") as f:
        json.dump(out,f,indent=2)
    print("valid_rows",len(rows),"bridge_failures",len(bad),"with_all_basic_gates",len(tight),flush=True)
    if bad:
        print("first_bad",bad[0],flush=True)
    if tight:
        print("first_tight",tight[0],flush=True)
    print("seconds",out["seconds"],flush=True)
