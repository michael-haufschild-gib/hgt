"""Locate channel regimes, validate an exact decimal witness, create phase data."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp
from tail_interventions import data_with_jets,atomic_jets
from tail_moment_dissection import channels,log_jets
from tail_adversary import validate
import clg_compensation as old


def phase_row(ts):
    mp.mp.dps = 65
    x0=mp.log(6/mp.pi)/2
    t=mp.mpf(ts)
    mass=old.moments(old.Bcoord(x0))[0]-1
    rows=[]
    for j in range(73):
        e=mp.mpf(10)**(-12+mp.mpf(j)/8)
        d=data_with_jets(x0+t,t,lambda x:atomic_jets(x,x0,mass,[mp.mpf(3),mp.mpf(255)],[1-e,e]))
        terms,h2=channels(d,mp.mpf(0))
        rows.append(dict(epsilon=mp.nstr(e,20),c3_scaled=mp.nstr(sum(terms)/mass**3,25),
            h2_scaled=mp.nstr(h2/mass**2,25),firsttwo_scaled=mp.nstr((terms[0]+terms[1])/mass**3,25)))
    return dict(t=ts,rows=rows)


def regime_chunk(chunk):
    mp.mp.dps=80
    rows=[]
    for r in chunk:
        A,t,l=map(mp.mpf,(r["left_A"],r["t"],r["l"]))
        x0=mp.log(A/mp.pi)/2
        mass=mp.mpf(r["mass"])
        gs=list(map(mp.mpf,r["nodes"]))
        ps=list(map(mp.mpf,r["probs"]))
        d=data_with_jets(x0+t,t,lambda x:atomic_jets(x,x0,mass,gs,ps))
        terms,h2=channels(d,l)
        action=d["q"]+l*d["dq"]
        pair=terms[0]+terms[1]
        ratio=-pair/terms[2] if pair<0 and terms[2]>0 else mp.mpf(0)
        rows.append(dict(seed=r["seed"],index=r["index"],l=r["l"],
            action=mp.nstr(action,25),pair=mp.nstr(pair,25),h2=mp.nstr(h2,25),
            adverse_ratio=mp.nstr(ratio,25),c3=mp.nstr(sum(terms),25)))
    return rows


if __name__=="__main__":
    start=time.monotonic()
    source=json.load(open("tail-channel-attack.json"))
    raw=[r for g in source["results"] for r in g["rows"]]
    chunks=[raw[i::8] for i in range(8)]
    with ProcessPoolExecutor(max_workers=8) as pool:
        regimes=[r for group in pool.map(regime_chunk,chunks) for r in group]
        phases=list(pool.map(phase_row,[mp.nstr(mp.mpf(10)**(-4+mp.mpf(i)/16),20) for i in range(41)]))
    case=dict(left_A="6",t=".003",g="255")
    row=dict(epsilon=".0000026",l="0")
    exact_decimal_validation=[validate(case,row,p) for p in (80,120)]
    negative=[r for r in regimes if mp.mpf(r["pair"])<0]
    positive_h2=[r for r in regimes if mp.mpf(r["h2"])>0]
    worst=max(regimes,key=lambda r:mp.mpf(r["adverse_ratio"]))
    summary=dict(negative_pair_count=len(negative),
        negative_pair_action_min=mp.nstr(min(mp.mpf(r["action"]) for r in negative),20),
        positive_pair_action_max=mp.nstr(max(mp.mpf(r["action"]) for r in regimes if mp.mpf(r["pair"])>=0),20),
        negative_c3_positive_h2=sum(mp.mpf(r["c3"])<0 for r in positive_h2),worst=worst)
    out=dict(seconds=time.monotonic()-start,summary=summary,regimes=regimes,phases=phases,
        exact_decimal_witness=dict(case=case,row=row,validation=exact_decimal_validation))
    with open("regime-diagnostics.json","w") as f:
        json.dump(out,f,indent=2)
    print(json.dumps(summary),flush=True)
    print("rational_epsilon_validation",json.dumps(exact_decimal_validation),flush=True)
    print("seconds",out["seconds"],flush=True)
