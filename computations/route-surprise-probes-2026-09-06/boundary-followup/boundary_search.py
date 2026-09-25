"""Condition source interventions on H''=0 instead of sampling past the boundary."""
import os
for key in ("OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS"):
    os.environ[key]="1"
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
import json
import time
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as mp
from tail_interventions import data_with_jets
from tail_moment_dissection import channels


def literal_moments(A):
    B=A-mp.mpf("1.5")
    out=[mp.mpf(0)]*4
    for n in range(2,41):
        g=mp.mpf(n*n-1)
        factor=mp.exp(-A*g)
        for j in range(4):
            ray=sum(mp.factorial(j)/mp.factorial(k)*g**k/B**(j-k+1) for k in range(j+1))
            out[j]+=factor*(n**4*g**j+mp.mpf("1.5")*n*n*g*ray)
    return out


def jets(A,m):
    z=1+m[0]
    mean=m[1]/z
    var=m[2]/z-mean**2
    k3=m[3]/z-3*mean*m[2]/z+2*mean**3
    return (mp.log1p(m[0]),-2*A*mean,4*A*A*var-4*A*mean,
        -8*A**3*k3+24*A*A*var-8*A*mean)


def make_family(left,ts,gs,baseline):
    A0=mp.pi if left=="pi" else mp.mpf(left)
    t,g=mp.mpf(ts),mp.mpf(gs)
    x0=mp.log(A0/mp.pi)/2
    u=x0+t
    if mp.pi*mp.exp(2*u)<6:
        return None
    mass=literal_moments(A0)[0]
    points=[u,u+t,u-t]
    scales=[mp.pi*mp.exp(2*x) for x in points]
    actual=[literal_moments(a) for a in scales] if baseline=="literal" else [
        [mass*3**j*mp.exp(-3*(a-A0)) for j in range(4)] for a in scales]
    remote=[[mass*g**j*mp.exp(-g*(a-A0)) for j in range(4)] for a in scales]
    def data(epsilon):
        values=[jets(a,[(1-epsilon)*m[j]+epsilon*n[j] for j in range(4)])
            for a,m,n in zip(scales,actual,remote)]
        return data_with_jets(u,t,lambda x:values[points.index(x)])
    return data,mass


def record(d,mass,epsilon,l):
    terms,H2=channels(d,l)
    t=d["t"]
    q=d["q"]+l*d["dq"]
    a,b,S,m=[d[k]+l*d["d"+k] for k in ("a","b","s","m")]
    H=a*t*m-(a+t*b)*S
    H1=d["da"]*t*m+a*t*d["dm"]-(d["da"]+t*d["db"])*S-(a+t*b)*d["ds"]
    A=-d["dq"]
    B=-H
    v=t*a
    coordinates={}
    if A and B and v:
        beta=(mp.exp(q)+1)/(mp.exp(q)-1)
        r=-t*d["da"]/(v*A)
        s=H1/(B*A)
        h=H2/(B*A*A)
        L=(6+4*beta)*r-2*(beta*beta-1)
        critical=(beta*beta-1)*(1-12*(r-beta/2)*(s-beta/2))/(3*L) if L else mp.nan
        coordinates={k:mp.nstr(val,30) for k,val in dict(beta=beta,r=r,s=s,h=h,
            kappa=s-r+h/(2*r),critical=critical,lower_slope=L).items()}
    gates=q>0 and a>0 and b>0 and S>0 and H<0 and H1>0 and H2>0
    return dict(epsilon=mp.nstr(epsilon,60),l=str(l),action=mp.nstr(q,30),
        c3=mp.nstr(sum(terms),40),c3_scaled=mp.nstr(sum(terms)/mass**3,35),
        h2=mp.nstr(H2,40),h2_scaled=mp.nstr(H2/mass**2,35),
        gates=bool(gates),counterexample=bool(gates and sum(terms)<0),coordinates=coordinates)


def run(spec):
    mp.mp.dps=75
    left,ts,gs,baseline=spec
    family=make_family(*spec)
    if family is None:
        return dict(spec=spec,skip="outside structural chamber")
    data,mass=family
    grid=[mp.mpf(0)]+[mp.mpf(10)**(-18+mp.mpf(j)/3) for j in range(55)]
    samples=[(e,channels(data(e),mp.mpf(0))[1]) for e in grid]
    crossings=[]
    for (lo,flo),(hi,fhi) in zip(samples[:-1],samples[1:]):
        if flo*fhi>=0:
            continue
        for _ in range(85):
            mid=(lo+hi)/2
            fm=channels(data(mid),mp.mpf(0))[1]
            if fm*flo>0:
                lo,flo=mid,fm
            else:
                hi,fhi=mid,fm
        center=(lo+hi)/2
        # Evaluate safely separated sides as well as the root enclosure.
        probes=[lo,hi,max(mp.mpf(0),center*(1-mp.mpf(".000001"))),
            min(mp.mpf(1),center*(1+mp.mpf(".000001")))]
        rows=[]
        for e in probes:
            d=data(e)
            for l in (mp.mpf(0),mp.mpf(".5"),mp.mpf(1)):
                if d["q"]+l*d["dq"]>0:
                    rows.append(record(d,mass,e,l))
        crossings.append(dict(bracket=[mp.nstr(lo,65),mp.nstr(hi,65)],rows=rows))
    return dict(spec=spec,mass=mp.nstr(mass,45),crossings=crossings,
        negative_scan_points=sum(f<0 for _,f in samples))


if __name__=="__main__":
    start=time.monotonic()
    specs=[(a,t,g,base) for a in ("pi","4","6","9","16")
        for t in (".00001",".0001",".001",".003",".01",".03",".1",".3",".8")
        for g in ("15","63","255","1023","4095") for base in ("atom3","literal")]
    results=[]
    with ProcessPoolExecutor(max_workers=8) as pool,open("boundary-results.jsonl","w") as stream:
        futures=[pool.submit(run,s) for s in specs]
        for future in as_completed(futures):
            result=future.result()
            results.append(result)
            stream.write(json.dumps(result)+"\n")
            stream.flush()
    rows=[r for result in results for crossing in result.get("crossings",[]) for r in crossing["rows"]]
    bad=[r for r in rows if r["counterexample"]]
    out=dict(seconds=time.monotonic()-start,results=results,
        crossing_count=sum(len(r.get("crossings",[])) for r in results),counterexamples=len(bad))
    with open("boundary-results.json","w") as f:
        json.dump(out,f,indent=2)
    print("families",len(results),"crossings",out["crossing_count"],"counterexamples",len(bad),flush=True)
    if bad:
        print("first_counterexample",json.dumps(bad[0]),flush=True)
    print("seconds",out["seconds"],flush=True)
