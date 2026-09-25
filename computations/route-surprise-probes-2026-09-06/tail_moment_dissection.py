"""Matched-moment spectral interventions and source invariant diagnostics."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
import math
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp
from tail_interventions import data_with_jets, atomic_jets
import clg_compensation as old


def model(m,g,e,k):
    if k==0:
        return [mp.mpf(3),g],[1-e,e]
    r = [m[j]-e*g**j for j in range(k+1)]
    if k==1:
        return [r[1]/r[0],g],[r[0],e]
    if k==2:
        excess = r[1]-3*r[0]
        if excess<=0:
            return None
        y = (r[2]-3*r[1])/excess
        if y<=3:
            return None
        wy = excess/(y-3)
        return [mp.mpf(3),y,g],[r[0]-wy,wy,e]
    det = r[0]*r[2]-r[1]**2
    if det<=0:
        return None
    s = (r[0]*r[3]-r[1]*r[2])/det
    p = (r[1]*r[3]-r[2]**2)/det
    disc = s*s-4*p
    if disc<=0:
        return None
    x,y = (s-mp.sqrt(disc))/2,(s+mp.sqrt(disc))/2
    wy = (r[1]-r[0]*x)/(y-x)
    return [x,y,g],[r[0]-wy,wy,e]


def log_jets(x,x0,mass,gs,ps,order=5):
    A,A0 = mp.pi*mp.exp(2*x),mp.pi*mp.exp(2*x0)
    stirling = [[0]*(order+1) for _ in range(order+1)]
    stirling[0][0] = 1
    for n in range(1,order+1):
        for j in range(1,n+1):
            stirling[n][j] = stirling[n-1][j-1]+j*stirling[n-1][j]
    z = [1+mass*sum(p*mp.exp(-(A-A0)*g) for g,p in zip(gs,ps))]
    for n in range(1,order+1):
        z.append(mass*sum(p*mp.exp(-(A-A0)*g)*2**n*
            sum(stirling[n][j]*(-A*g)**j for j in range(1,n+1)) for g,p in zip(gs,ps)))
    f = [mp.log(z[0])]
    for n in range(1,order+1):
        f.append((z[n]-sum(math.comb(n-1,j-1)*f[j]*z[n-j] for j in range(1,n)))/z[0])
    return f


def channels(d,l):
    t = d["t"]
    a,b,s,m = [d[v]+l*d["d"+v] for v in ("a","b","s","m")]
    q = d["q"]+l*d["dq"]
    h = a*t*m-(a+t*b)*s
    h1 = d["da"]*t*m+a*t*d["dm"]-(d["da"]+t*d["db"])*s-(a+t*b)*d["ds"]
    h2 = 2*(d["da"]*t*d["dm"]-(d["da"]+t*d["db"])*d["ds"])
    ex = mp.exp(q)
    r = ex-1
    r1 = -ex*d["dq"]/r**2
    r2 = ex*(ex+1)*d["dq"]**2/r**3
    r3 = -ex*(ex**2+4*ex+1)*d["dq"]**3/r**4
    v,dv = t*a,t*d["da"]
    w1 = 10*dv+8*(dv/r+v*r1)
    w2 = 8*(2*dv*r1+v*r2)
    w3 = 8*(3*dv*r2+v*r3)
    return [-w3*h,-3*w2*h1,-3*w1*h2],h2


def run(spec):
    ts,gs = spec
    mp.mp.dps = 65
    a0,t,g = mp.mpf(6),mp.mpf(ts),mp.mpf(gs)
    x0 = mp.log(a0/mp.pi)/2
    u = x0+t
    z,m1,m2,m3 = old.moments(old.Bcoord(x0))
    mass = z-1
    m = [mp.mpf(1),m1/mass,m2/mass,m3/mass]
    rows = []
    for k in range(4):
        for power in range(-14,-2):
            for leading in (1,3):
                e = leading*mp.mpf(10)**power
                made = model(m,g,e,k)
                if made is None:
                    continue
                nodes,probs = made
                if min(nodes)<3 or min(probs)<0:
                    continue
                mismatch = max(abs(sum(p*h**j for h,p in zip(nodes,probs))-m[j]) for j in range(k+1))
                d = data_with_jets(u,t,lambda x:atomic_jets(x,x0,mass,nodes,probs))
                value = old.comp3(d,mp.mpf(0))[0]
                contributions,h2 = channels(d,mp.mpf(0))
                invariants = []
                for j in range(9):
                    x = x0+2*t*j/8
                    f = log_jets(x,x0,mass,nodes,probs)
                    invariants.append(dict(x=mp.nstr(x,20),
                        seam=mp.nstr(f[2]*f[5]-2*f[3]*f[4],25),
                        curvature=mp.nstr(3*f[3]**2-2*f[2]*f[4],25)))
                rows.append(dict(t=ts,g=gs,matched_moments=k,epsilon=mp.nstr(e,15),
                    nodes=[mp.nstr(h,35) for h in nodes],probs=[mp.nstr(p,35) for p in probs],
                    moment_residual=mp.nstr(mismatch,10),c3=mp.nstr(value,35),
                    channels=[mp.nstr(v,30) for v in contributions],h2=mp.nstr(h2,25),invariants=invariants))
    return dict(t=ts,g=gs,mass=mp.nstr(mass,35),moments=[mp.nstr(v,35) for v in m],rows=rows)


if __name__ == "__main__":
    start = time.monotonic()
    specs = [(t,g) for t in (".0001",".001",".003",".01") for g in ("63","255","1023")]
    with ProcessPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run,specs))
    out = dict(seconds=time.monotonic()-start,results=results)
    with open("tail-moment-dissection.json","w") as f:
        json.dump(out,f,indent=2)
    rows = [r for group in results for r in group["rows"]]
    for k in range(4):
        sub = [r for r in rows if r["matched_moments"]==k]
        neg = [r for r in sub if mp.mpf(r["c3"])<0]
        print("moments",k,"admissible",len(sub),"negative",len(neg),flush=True)
        if neg:
            r = neg[0]
            print("first",{key:r[key] for key in ("t","g","epsilon","nodes","probs","c3","h2")},flush=True)
    print("seconds",out["seconds"],flush=True)
