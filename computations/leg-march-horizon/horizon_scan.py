#!/usr/bin/env python3
# March-horizon scan on the harmonic section carrier delta_j = c/j, poles t_1..t_d.
# Equilibrium s_i in gap i solves G_i(s) = -d (G strictly increasing in s).
# March monotone at i iff DeltaG = G_{i+1}(s_i) - G_i(s_i) > 0.
# Pre-registered predictions [CONJECTURE]:
#  P1: a horizon i*(c,d) exists in the inner half: DeltaG < 0 for i <= i*, >= 0 above.
#  P2: i*/d ~ constant in d; theta-mechanism predicts i*/d ~ 0.05 (c=2),
#      log-mechanism predicts i*/d ~ 0.009 (c=2); measured value identifies the mechanism.
#  P3: past the horizon DeltaG stays negative down to i=1 (no re-entry).
#  P4: theta*(i) = s_i/delta_{i+1} < 1/2 everywhere.
#  P5: i*(c)/d increases with c.
import math, json
def coth(x): return 1.0/math.tanh(x)
def scan(c, d, imax):
    t=[0.0]*(d+1)
    for j in range(1,d): t[j+1]=t[j]+c/j
    def G(i,s):
        x=t[i+1]-s
        acc=0.0
        for m in range(1,i+1): acc+=coth((x-t[m])/2)
        for m in range(i+1,d+1): acc-=coth((t[m]-x)/2)
        return acc
    rows=[]
    for i in range(1,imax):
        dlt=t[i+1]-t[i]
        lo,hi=dlt*1e-12,dlt*(1-1e-12)
        for _ in range(70):
            mid=0.5*(lo+hi)
            if G(i,mid) < -d: lo=mid
            else: hi=mid
        s=0.5*(lo+hi)
        d2=t[i+2]-t[i+1]
        th=s/d2
        dG=(G(i+1,s)-G(i,s)) if s<d2 else None
        rows.append((i,th,dG))
    return rows
for c in (1,2,3):
    for d in (200,1000,5000):
        imax = d-2 if d<=1000 else d//3
        rows=scan(c,d,imax)
        val=[r for r in rows if r[2] is not None]
        neg=[r for r in val if r[2]<0]
        istar=max((r[0] for r in neg), default=None)
        reentry=[r[0] for r in val if istar and r[0]<istar and r[2]>0]
        res=dict(istar=istar, istar_over_d=(istar/d if istar else None),
                 n_neg=len(neg), reentry=len(reentry),
                 theta_max=round(max(r[1] for r in rows),4),
                 theta_at_istar=(round(rows[istar-1][1],4) if istar else None),
                 dG_at_i1=round(val[0][2],4) if val else None,
                 dG_min=round(min(r[2] for r in val),4),
                 s_overflow=sum(1 for r in rows if r[2] is None))
        print(f"c={c},d={d}", json.dumps(res), flush=True)
        step=max(1,len(rows)//30)
        prof=[(r[0],round(r[1],3),(round(r[2],3) if r[2] is not None else None)) for r in rows[::step]]
        print(f"c={c},d={d} profile {prof}", flush=True)
print("DONE")
