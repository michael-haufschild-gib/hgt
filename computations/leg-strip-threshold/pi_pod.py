import math
def coth(x): return 1.0/math.tanh(x)
def poles(c,d):
    T=[0.0]*(d+2)
    for j in range(1,d+1): T[j+1]=T[j]+c/j
    return T
def theta(T,d,i,level):
    a,b=T[i],T[i+1]
    def F(x): return sum(coth((x-T[j])/2) for j in range(1,d+1))
    lo,hi=a+1e-13*(b-a),b-1e-13*(b-a)
    for _ in range(80):
        mid=(lo+hi)/2
        if F(mid)>level: lo=mid
        else: hi=mid
    return (b-(lo+hi)/2)/(b-a)
def theta_max(c,d):
    # peak is at i ~ (pi/4)sqrt(d); scan a window around it, cheap
    T=poles(c,d); c0=int(0.9*math.sqrt(d)); w=int(0.6*math.sqrt(d))+5
    best=0;bi=0
    for i in range(max(1,c0-w),c0+w):
        th=theta(T,d,i,-d)
        if th>best: best=th;bi=i
    return best,bi
print(f"1/pi={1/math.pi:.6f}  pi/4={math.pi/4:.6f}",flush=True)
print("c=2 margin scaling:",flush=True)
for d in (16000,32000,64000):
    m,bi=theta_max(2.0,d)
    print(f"  d={d}: margin*sqrt(d)={(0.5-m)*math.sqrt(d):.5f}  i_peak/sqrt(d)={bi/math.sqrt(d):.4f}",flush=True)
print("threshold c<2 crosses 1/2 at large d?:",flush=True)
for c in (1.98,1.99,2.0):
    m,bi=theta_max(c,32000)
    print(f"  c={c} d=32000: theta_max={m:.5f} strip={'YES' if m>0.5 else 'no'}",flush=True)
