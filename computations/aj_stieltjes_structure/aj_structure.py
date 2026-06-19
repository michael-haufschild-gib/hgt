import mpmath as mp
mp.mp.dps = 60
# a_j = [s^j](zeta'/zeta)(s) at s=0
f = lambda s: mp.zeta(s,1,1)/mp.zeta(s)
a = mp.taylor(f, 0, 4)
L2pi = mp.log(2*mp.pi)
gE = mp.euler
g1 = mp.stieltjes(1)   # Stieltjes gamma_1
pi2 = mp.pi**2
z3  = mp.zeta(3)
print("a_0 =", mp.nstr(a[0],30), " log(2pi)=", mp.nstr(L2pi,30))
print("a_1 =", mp.nstr(a[1],30))
print("a_2 =", mp.nstr(a[2],30))
def pslq(name, val, basis, names):
    rel = mp.pslq([val]+basis, maxcoeff=10**8, maxsteps=10**5)
    if rel is None: print("  %s: no relation (basis %s)"%(name, names)); return
    print("  %s: rel=%s  over [%s]"%(name, rel, ", ".join(["val"]+names)))
# a_1 basis
pslq("a_1", a[1], [mp.mpf(1), gE, L2pi, gE*L2pi, gE**2, L2pi**2, pi2, g1],
     ["1","gE","L2pi","gE*L2pi","gE^2","L2pi^2","pi^2","g1"])
# a_2 basis (cubic combos + Stieltjes)
g2 = mp.stieltjes(2)
z2 = mp.zeta(2)
pslq("a_2", a[2], [mp.mpf(1), gE, L2pi, gE*L2pi, gE**2, L2pi**2, pi2, g1, gE**3, L2pi**3, gE*pi2, L2pi*pi2, gE*g1, L2pi*g1, z3, g2],
     ["1","gE","L2pi","gE*L2pi","gE^2","L2pi^2","pi^2","g1","gE^3","L2pi^3","gE*pi2","L2pi*pi2","gE*g1","L2pi*g1","z3","g2"])
