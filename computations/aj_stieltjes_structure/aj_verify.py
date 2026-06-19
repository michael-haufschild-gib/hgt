import mpmath as mp
mp.mp.dps = 80
f = lambda s: mp.zeta(s,1,1)/mp.zeta(s)
a = mp.taylor(f, 0, 4)
gE = mp.euler; g1 = mp.stieltjes(1); g2 = mp.stieltjes(2)
# discovered closed forms:
a0_f = mp.log(2*mp.pi)
a1_f = mp.zeta(2)/2 - gE**2 - 2*g1                      # = pi^2/12 - gE^2 - 2 g1
a2_f = mp.zeta(3) - gE**3 - 3*gE*g1 - mp.mpf(3)/2*g2
print("a_0: |a-formula| =", mp.nstr(abs(a[0]-a0_f),5), "   a_0 = log(2pi)")
print("a_1: |a-formula| =", mp.nstr(abs(a[1]-a1_f),5), "   a_1 = zeta(2)/2 - gamma_E^2 - 2*gamma_1")
print("a_2: |a-formula| =", mp.nstr(abs(a[2]-a2_f),5), "   a_2 = zeta(3) - gamma_E^3 - 3 gamma_E gamma_1 - (3/2) gamma_2")
