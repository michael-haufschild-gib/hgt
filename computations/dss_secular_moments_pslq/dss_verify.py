import mpmath as mp
mp.mp.dps = 220
f = lambda s: mp.zeta(s,1,1)/mp.zeta(s)
a = mp.taylor(f, 0, 10)
def P(k): return 1 - ((-1)**k)*mp.zeta(k)/mp.mpf(2)**k - a[k-1]
Ps = [P(k) for k in range(2,9)]
g = mp.euler; pi2 = mp.pi**2; z3 = mp.zeta(3)
def pslq(name, vec):
    rel = mp.pslq(vec, maxcoeff=10**12, maxsteps=10**6)
    print("  %-42s : %s"%(name, "NO relation" if rel is None else ("rel="+str(rel))))
print("dps=220, maxcoeff=1e12, guard 11*12=132 < 220 (precision-safe):")
pslq("{P_2..P_8}", Ps)
pslq("{P_2..P_8, 1}", Ps+[mp.mpf(1)])
pslq("{P_2..P_8, 1, pi^2, zeta3, gammaE}", Ps+[mp.mpf(1),pi2,z3,g])
