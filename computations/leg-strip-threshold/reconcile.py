import math
def coth(x): return 1.0/math.tanh(x)
def poles(c,d):
    T=[0.0]*(d+2)
    for j in range(1,d+1): T[j+1]=T[j]+c/j
    return T
def theta(c,d,i,npoles,level):
    T=poles(c,d); a,b=T[i],T[i+1]
    def F(x): return sum(coth((x-T[j])/2) for j in range(1,npoles+1))
    lo,hi=a+1e-13*(b-a),b-1e-13*(b-a)
    for _ in range(90):
        mid=(lo+hi)/2
        if F(mid)>level: lo=mid
        else: hi=mid
    return (b-(lo+hi)/2)/(b-a)
# Convention A: d poles T_1..T_d, level -d
# Convention B: d+1 poles T_1..T_{d+1}, level -(d+1)
print("i=1 theta* under conventions (c=2, d=400):")
print("  A (d poles, lvl -d):     ", round(theta(2,400,1,400,-400),4))
print("  B (d+1 poles, lvl -(d+1)):", round(theta(2,400,1,401,-401),4))
print("  A' (d poles, lvl -d, but only sum over existing):")
# careful: with d poles, T_{d+1} doesn't exist. Use npoles=d.
print()
print("theta_max over edge i=1..30, convention A (d poles, level -d):")
for c in (1.0,1.5,2.0,2.5,3.0):
    for d in (200,800,3000):
        th=[theta(c,d,i,d,-d) for i in range(1,31)]
        mx=max(th); am=th.index(mx)+1
        print(f"  c={c} d={d:4d}: theta_max={mx:.4f} at i={am}  (i=1:{th[0]:.4f})  strip={'YES' if mx>0.5 else 'no'}")
    print()
