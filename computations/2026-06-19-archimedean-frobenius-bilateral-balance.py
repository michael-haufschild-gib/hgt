"""
Step-3 certificate for moonshot-2pi-monodromy-frobenius (archimedean one-sided Frobenius).

Conjecture (C): the unitary/bilateral completion of the one-sided archimedean shift is the
BALANCE of the two FE-paired one-sided ladders (s-side and (1-s)-side), and it is unitary
(pure phase, modulus 1) EXACTLY on the FE-fixed locus Re(s)=1/2 (the critical line).

Objects:
  G(s) = pi^{-s/2} Gamma(s/2)               # archimedean factor Gamma_R(s); poles at s in -2N (one-sided ladder)
  R(s) = G(s)/G(1-s)                          # FE-ratio of the two one-sided ladders
  imbalance(s) = log|R(s)|                     # 0  <=> unitary/balanced

Two predictions to certify:
  (1) imbalance(s) = 0  iff  Re(s)=1/2 ; sign-definite and strictly monotone in sigma off the line.
  (2) the two ladder GROUND STATES (s/2 and (1-s)/2) coincide exactly at s=1/2:
         gap(s) = s/2 - (1-s)/2 = s - 1/2   ->  Re gap = sigma - 1/2  (vanishes on the line).
"""
import mpmath as mp
mp.mp.dps = 40

def G(s):
    return mp.power(mp.pi, -s/2) * mp.gamma(s/2)

def imbalance(s):
    return mp.log(abs(G(s)/G(1-s)))

print("== Prediction (1): imbalance(sigma+it) vanishes iff sigma=1/2, monotone off-line ==")
for t in [mp.mpf('1'), mp.mpf('10'), mp.mpf('50')]:
    print(f"\n t = {t}")
    print(f"   {'sigma':>8} {'log|R|':>22} {'sign':>6}")
    prev = None
    mono = True
    for k in range(1, 10):
        sigma = mp.mpf(k)/10
        val = imbalance(sigma + 1j*t)
        sign = '0' if abs(val) < mp.mpf('1e-30') else ('+' if val > 0 else '-')
        print(f"   {mp.nstr(sigma,4):>8} {mp.nstr(val,16):>22} {sign:>6}")
        if prev is not None and not (val > prev):
            mono = False
        prev = val
    print(f"   monotone increasing in sigma? {mono}")
    # exact zero at 1/2
    z = imbalance(mp.mpf('0.5') + 1j*t)
    print(f"   imbalance at sigma=1/2 : {mp.nstr(z,6)}   (=0 to {mp.mp.dps} dps: {abs(z) < mp.mpf('1e-30')})")

print("\n== Prediction (2): ladder ground-state gap = s-1/2, real part vanishes on the line ==")
for s in [mp.mpf('0.3')+1j, mp.mpf('0.5')+1j, mp.mpf('0.7')+1j]:
    gap = s/2 - (1-s)/2
    print(f"   s={mp.nstr(s,5):>14}  gap=s/2-(1-s)/2={mp.nstr(gap,6):>14}  Re(gap)={mp.nstr(mp.re(gap),6)}  (=s-1/2 check: {mp.nstr(s-mp.mpf('0.5'),6)})")

print("\n== Cross-check: on the line the FE-ratio is a pure phase (|R|=1, arg=R-S phase) ==")
for t in [mp.mpf('1'), mp.mpf('14.134725'), mp.mpf('50')]:
    s = mp.mpf('0.5') + 1j*t
    R = G(s)/G(1-s)
    print(f"   t={mp.nstr(t,8):>12}  |R|={mp.nstr(abs(R),20)}   arg(R)={mp.nstr(mp.arg(R),8)}")
