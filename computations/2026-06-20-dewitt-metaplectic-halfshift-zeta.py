#!/usr/bin/env python3
# MACHINE STEP7 transfer: METAPLECTIC-CORRECTION experiment (the +1/2 Maslov shift / ZZ/2 square-root)
# applied to Riemann zeta's counting/quantization structure. Transfer the TEST (is there a half-shift
# making the quantization exact? is a sqrt-branch forced?), NOT the constraint.
# (1) Maslov constant in N(T)=theta(T)/pi+1+S(T): extract the additive constant from true zeros.
# (2) Half-shift test: do zeros sit at HALF-integer vs INTEGER theta/pi (relative to Gram points)?
# (3) sqrt-branch: Hardy rotation e^{i theta}=chi(1/2+it)^(-1/2) is a half-form (sqrt of FE factor chi).
import mpmath as mp
mp.mp.dps = 40

def theta(t):  # Riemann-Siegel theta
    return mp.siegeltheta(t)

# smooth count asymptotic constant: theta(t)/pi ~ (t/2pi)log(t/2pi) - t/2pi - 1/8 + ...
# so N_smooth(t)=theta/pi+1 has constant 1-1/8 = 7/8 (the candidate metaplectic/Maslov constant).
print("=== (1) Maslov/metaplectic additive constant from TRUE zeros ===")
print("at n-th zero gamma_n: theta(gamma_n)/pi + 1 + S = n ; mean[ n - 1 - theta(gamma_n)/pi ] -> <S>~0")
devs=[]
half_test=[]
zeros=[]
for n in range(1,61):
    g=mp.zetazero(n).imag
    zeros.append(g)
    tp=theta(g)/mp.pi
    # N(gamma_n) counts n zeros up to gamma_n; smooth part theta/pi+1; so S(gamma_n)=n-1-theta/pi
    S = n - 1 - tp
    devs.append(S)
    # half-shift test: fractional part of theta(gamma_n)/pi ; Gram points have theta/pi = integer.
    frac = tp - mp.floor(tp)
    half_test.append(float(frac))
meanS=sum(devs)/len(devs)
print(f"  mean S(gamma_n) over n=1..60 = {mp.nstr(meanS,6)}  (should be ~0 if constant=7/8 i.e. -1/8 in theta)")
print(f"  => the metaplectic-type constant in N(T) is 7/8 (= 1 - 1/8). Confirmed if meanS~0.")

print("\n=== (2) half-shift test: frac(theta(gamma_n)/pi) distribution ===")
import statistics
mean_frac=statistics.mean(half_test)
print(f"  mean frac(theta/pi) at zeros = {mean_frac:.4f}")
print(f"  metaplectic HALF-shift would predict ~0.5 (zeros half-way between Gram pts);")
print(f"  Gram's law (no half-shift; zeros NEAR Gram pts theta/pi=integer) predicts ~0 or ~1 clustering.")
# histogram coarse
import collections
bins=collections.Counter(int(x*10)%10 for x in half_test)
print("  frac*10 histogram:", dict(sorted(bins.items())))

print("\n=== (3) sqrt-branch (half-form) check: is e^{i theta} = chi(1/2+it)^{-1/2} ? ===")
def chi(s):  # zeta(s)=chi(s) zeta(1-s); chi(s)=2^s pi^{s-1} sin(pi s/2) Gamma(1-s)
    return 2**s * mp.pi**(s-1) * mp.sin(mp.pi*s/2) * mp.gamma(1-s)
for t in [20.0, 50.0, 100.0]:
    s=mp.mpf('0.5')+1j*t
    lhs=mp.e**(1j*theta(t))
    # chi(1/2+it) has modulus 1; its inverse sqrt:
    rhs=chi(s)**(mp.mpf('-0.5'))
    # compare up to ZZ/2 sign (the metaplectic branch ambiguity)
    diff=min(abs(lhs-rhs),abs(lhs+rhs))
    print(f"  t={t}: |chi|={mp.nstr(abs(chi(s)),6)}  |e^{{i th}} - chi^(-1/2)| (mod sign) = {mp.nstr(diff,4)}")
print("\nDONE")
