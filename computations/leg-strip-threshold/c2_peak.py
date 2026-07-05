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
    for _ in range(90):
        mid=(lo+hi)/2
        if F(mid)>level: lo=mid
        else: hi=mid
    return (b-(lo+hi)/2)/(b-a)
# full inner-half theta profile, find true max
print("full theta* peak over ALL i (level -d):")
for c in (1.8,1.9,2.0,2.05,2.1):
    for d in (1000,4000):
        T=poles(c,d)
        # scan step to keep it fast
        step=max(1,d//400)
        best=0; bi=0
        for i in range(1,d-1,step):
            th=theta(T,d,i,-d)
            if th>best: best=th; bi=i
        # refine near bi
        for i in range(max(1,bi-step),min(d-1,bi+step)):
            th=theta(T,d,i,-d)
            if th>best: best=th; bi=i
        print(f"  c={c} d={d:5d}: theta_max={best:.4f} at i={bi} (i/d={bi/d:.3f})  strip={'YES' if best>0.5 else 'no'}")
    print()
