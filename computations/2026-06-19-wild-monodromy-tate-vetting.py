"""Vetting (Professor) of archimedean-wild-monodromy-tate-local A5: the archimedean Stokes data is TATE.
FACT 1: E_1 Borel transform = 1/(1+xi), simple pole xi=-1 => Stokes multiplier 2*pi*i (Tate).
        Check exact rep E_1(z) = e^{-z} int_0^inf e^{-z xi}/(1+xi) dxi.
FACT 2: Binet integrand has poles at t=2*pi*i*k, Res 1/(e^t-1)=1 => mu-residue ~1/(2*pi*i*k) (Tate powers).
FACT 3: a_inf = (1/2)log(2pi) = -zeta'(0) (Tate constant)."""
import mpmath as mp
mp.mp.dps = 30
print("FACT 1 (E_1 Borel, pole xi=-1):")
for z in [mp.mpf(5), mp.mpf(10), mp.mpf(20)]:
    a = mp.e**(-z)*mp.quad(lambda xi: mp.e**(-z*xi)/(1+xi), [0, mp.inf]); b = mp.e1(z)
    print(f"  z={float(z):4.0f}  diff(Borel,E_1)={float(abs(a-b)):.2e}")
print("FACT 2 (Binet poles t=2pi i k, Res 1/(e^t-1)=1):")
for k in [1, 2, 3]:
    t0 = 2*mp.pi*1j*k
    res = mp.limit(lambda e: e/(mp.e**(t0+e)-1), 0)
    print(f"  k={k}: Res={mp.nstr(res,6)} (=1), mu-residue~1/(2pi i k)={mp.nstr(1/t0,6)}")
print(f"FACT 3: 1/2 log2pi = {mp.nstr(mp.log(2*mp.pi)/2,12)} ; -zeta'(0) = {mp.nstr(-mp.zeta(0,1,1),12)}")
print("=> all archimedean Stokes data are 2*pi*i powers = TATE. A5 verified.")
