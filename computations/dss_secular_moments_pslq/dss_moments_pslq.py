import mpmath as mp
mp.mp.dps = 120
# P_k = 1 - (-1)^k zeta(k)/2^k - a_{k-1},  a_j = [s^j](zeta'/zeta)(0)
f = lambda s: mp.zeta(s,1,1)/mp.zeta(s)
a = mp.taylor(f, 0, 10)
def P(k): return 1 - ((-1)**k)*mp.zeta(k)/mp.mpf(2)**k - a[k-1]
Ps = [P(k) for k in range(2,9)]   # P_2..P_8
print("secular moments P_2..P_8 (dps=120):")
for k,v in zip(range(2,9),Ps): print("  P_%d = %s"%(k, mp.nstr(v,20)))

def pslq(name, vec, names):
    rel = mp.pslq(vec, maxcoeff=10**12, maxsteps=10**6)
    if rel is None: print("  %-42s : NO relation (height<=1e12)"%name)
    else:
        resid = sum(mp.mpf(rel[i])*vec[i] for i in range(len(vec)))
        print("  %-42s : rel=%s resid=%s [%s]"%(name, rel, mp.nstr(abs(resid),3), ",".join(names)))

print()
print("DSS numerical test (precision guard: n*log10(1e12) << 120 dps):")
pslq("{P_2..P_8}", Ps, ["P%d"%k for k in range(2,9)])
pslq("{P_2..P_8, 1}", Ps+[mp.mpf(1)], ["P%d"%k for k in range(2,9)]+["1"])
g = mp.euler; pi2 = mp.pi**2; z3 = mp.zeta(3)
pslq("{P_2..P_8, 1, pi^2, zeta3, gammaE}", Ps+[mp.mpf(1),pi2,z3,g],
     ["P%d"%k for k in range(2,9)]+["1","pi2","z3","gE"])
