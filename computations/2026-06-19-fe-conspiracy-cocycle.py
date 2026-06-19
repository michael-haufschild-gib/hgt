"""
FE-conspiracy cocycle — numeric pre-certification (card: archimedean-prime-cross-term).

Claims certified (dps=30):
  (1) FE:           Lambda(s) = Lambda(1-s),  Lambda = Gamma_R(s)*zeta(s),  Gamma_R(s)=pi^{-s/2}Gamma(s/2)
  (2) cocycle:      rho_inf(s) * rho_zeta(s) = 1,
                    rho_inf = Gamma_R(1-s)/Gamma_R(s) = chi(s)   (archimedean FE-defect)
                    rho_zeta = zeta(1-s)/zeta(s) = 1/chi(s)      (prime-factor FE-defect)
  (3) purely-arch:  chi(s) = pi^{s-1/2} * Gamma((1-s)/2)/Gamma(s/2)   (only pi, Gamma; NO integer primes)
  (4) non-horizontal: d/ds log chi != 0  (chi is not a d_s-horizontal gauge => iota_inf is not an M_inf automorphism)

Reading: the entire FE-asymmetry is carried by the archimedean factor chi; the prime lane
contributes nothing to the FE-defect (its iota-action is the free inversion x_p -> 1/x_p plus a
sigma_p shift). Hence the archimedean x prime cross-term cocycle is purely archimedean => BRIDGE.
"""
import mpmath as mp
mp.mp.dps = 30

def GR(s):                       # completed real Gamma factor
    return mp.power(mp.pi, -s/2) * mp.gamma(s/2)
def Lam(s):
    return GR(s) * mp.zeta(s)

pts = [mp.mpf('2'), mp.mpc('0.5','14.134725'), mp.mpc('0.3','7'),
       mp.mpc('0.8','25'), mp.mpf('4'), mp.mpc('0.5','40')]

print("=== FE-conspiracy cocycle numeric pre-cert (dps=30) ===")
for s in pts:
    chi   = GR(1-s)/GR(s)
    rzeta = mp.zeta(1-s)/mp.zeta(s)
    fe    = abs(Lam(s)-Lam(1-s))                                   # (1)
    prod  = chi*rzeta                                             # (2)
    chiA  = mp.power(mp.pi, s-mp.mpf('0.5'))*mp.gamma((1-s)/2)/mp.gamma(s/2)  # (3)
    dlog  = mp.diff(lambda z: mp.log(GR(1-z)/GR(z)), s)            # (4) d/ds log chi
    print(f"s={complex(s):>14.6g} | FE={mp.nstr(fe,3):>9} | rho_inf*rho_zeta={mp.nstr(prod,10)} "
          f"| |chi-archForm|={mp.nstr(abs(chi-chiA),3):>9} | d_s log chi={mp.nstr(dlog,6)}")
