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
def theta_max(c,d):
    T=poles(c,d); step=max(1,d//500); best=0;bi=0
    for i in range(1,d//2,step):
        th=theta(T,d,i,-d)
        if th>best: best=th;bi=i
    for i in range(max(1,bi-step),bi+step):
        th=theta(T,d,i,-d)
        if th>best:best=th;bi=i
    return best,bi
# 1) threshold precision: c very near 2, large d
print("theta_max near c=2 (does it exceed 1/2?):")
for c in (1.95,1.98,2.0,2.02):
    row=[]
    for d in (2000,8000,20000):
        m,bi=theta_max(c,d); row.append(f"d={d}:{m:.4f}")
    print(f"  c={c}: "+"  ".join(row))
# 2) marginal scaling at c=2: (1/2 - theta_max) vs d ; and peak location i_peak/sqrt(d)
print()
print("c=2 marginal scaling: margin=1/2-theta_max, i_peak/sqrt(d):")
for d in (1000,2000,4000,8000,16000):
    m,bi=theta_max(2.0,d)
    print(f"  d={d:6d}: margin={0.5-m:.5f}  margin*sqrt(d)={(0.5-m)*math.sqrt(d):.4f}  i_peak={bi} i/sqrt(d)={bi/math.sqrt(d):.3f}")
