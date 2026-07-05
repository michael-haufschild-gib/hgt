# (a) Extend htail certification to theta in [0.15,0.8] (expect: holds, worst at small theta).
# (b) c-boundary: min_i DeltaG(s_i) vs c at d=500. Pre-registered [CONJECTURE]:
#     margin = dGmin - 2 decays ~ geometrically in c, stays positive for all c (never crosses 2).
import math
def coth(x): return 1.0/math.tanh(x)
def csch2(x): s=math.sinh(x); return 1.0/(s*s)
# (a)
def htail_margin(c,d,i,theta):
    t=[0.0]*(d+1)
    for j in range(1,d): t[j+1]=t[j]+c/j
    s=theta*(t[i+2]-t[i+1]); R=d-i-2
    TB=TA=0.0
    for k in range(R):
        oldB=t[i+1]-t[i-k]-s; newB=t[i+2]-t[i+1-k]-s
        newA=t[i+3+k]-t[i+2]+s; oldA=t[i+2+k]-t[i+1]+s
        TB+=((oldB-newB)/2)*csch2(oldB/2); TA+=((oldA-newA)/2)*csch2(newA/2)
    return TB-TA
worst=None
for c in (1,1.5,2,3):
    for d in (100,200,400):
        for frac in (0.5,0.6,0.75,0.9,0.97):
            i=int(d*frac)
            if d-i-2<1 or d-i-2>i: continue
            for th in (0.15,0.3,0.5,0.6,0.7,0.8):
                m=htail_margin(c,d,i,th)
                if worst is None or m<worst[0]: worst=(m,c,d,frac,th)
print("(a) htail extended window worst margin:", tuple(round(x,4) if isinstance(x,float) else x for x in worst))
# (b)
def scan_min(c,d):
    t=[0.0]*(d+1)
    for j in range(1,d): t[j+1]=t[j]+c/j
    def G(i,s):
        x=t[i+1]-s
        return sum(coth((x-t[m])/2) for m in range(1,i+1))-sum(coth((t[m]-x)/2) for m in range(i+1,d+1))
    best=None; thmax=0.0
    for i in range(1,d-2):
        dlt=t[i+1]-t[i]; lo,hi=dlt*1e-12,dlt*(1-1e-12)
        for _ in range(60):
            mid=0.5*(lo+hi)
            if G(i,mid)<-d: lo=mid
            else: hi=mid
        s=0.5*(lo+hi); d2=t[i+2]-t[i+1]
        thmax=max(thmax,s/d2)
        if s<d2:
            dG=G(i+1,s)-G(i,s)
            if best is None or dG<best[0]: best=(dG,i)
    return best, thmax
d=500
for c in (3.5,4,5,6,8,12):
    (dGmin,imin),thmax=scan_min(c,d)
    print(f"(b) c={c}: dG_min={dGmin:.4f} at i={imin} (i/d={imin/d:.2f})  margin={dGmin-2:+.4f}  theta_max={thmax:.3f}")
