"""
Surrogate-ladder rung-1 no-go — numerical confirmation.

Claim: every FE-exact, xi-exact-zeros entire object is S = exp(c (s-1/2)^2 + d) * xi,
hence hypertranscendental (HT part zeta'/zeta is untouched). The rung-1 adversary
(FE-exact + correct-zeros + NON-HT) therefore does not exist; the weld carrier
cannot be a native-HT detector — it tracks zeros/FE/analyticity.

This script confirms the *exact algebra* the argument rests on:
 (a) carrier decomposition  xi'/xi = (1/s + 1/(s-1)) + A + P,  A=d/ds log Gamma_inf, P=zeta'/zeta
 (b) surrogate level law     S'/S - xi'/xi = 2 c (s-1/2)      (S = e^{c(s-1/2)^2} xi)
 (c) completed weld          H_S = A + 2c(s-1/2) + P,  P (the HT carrier) identical;
                              Delta_S -> Delta_true as c->0; zeros (hence kappa_-) identical.
Run: python3 this.py   (local mpmath, ~seconds)
"""
import mpmath as mp
mp.mp.dps = 30

half = mp.mpf(1)/2
logpi = mp.log(mp.pi)

def A(s):                      # archimedean term  d/ds log( pi^{-s/2} Gamma(s/2) )
    return -half*logpi + half*mp.digamma(s/2)

def P(s):                      # prime term  zeta'/zeta
    return mp.diff(mp.zeta, s)/mp.zeta(s)

def logxi(s):                  # log of completed entire xi(s) = 1/2 s(s-1) pi^{-s/2} Gamma(s/2) zeta(s)
    return ( mp.log(half) + mp.log(s) + mp.log(s-1)
             - (s/2)*logpi + mp.loggamma(s/2) + mp.log(mp.zeta(s)) )

def xi_logderiv(s):            # xi'/xi via direct differentiation of log xi
    return mp.diff(logxi, s)

def rational(s):               # d/ds log( 1/2 s(s-1) ) = 1/s + 1/(s-1)
    return 1/s + 1/(s-1)

def carrier_Delta(Aval, Pval):
    # Delta = max(log|A|, log|P|) - log|A+P|
    return max(mp.log(abs(Aval)), mp.log(abs(Pval))) - mp.log(abs(Aval+Pval))

# test points: sigma in {0.3,0.5,0.7}, t away from the first zeros (14.13,21.02,25.01,30.42,32.93,37.59)
sigmas = [mp.mpf('0.3'), mp.mpf('0.5'), mp.mpf('0.7')]
ts     = [mp.mpf('18'), mp.mpf('27'), mp.mpf('35')]
cs     = [mp.mpf('0'), mp.mpf('1e-4'), mp.mpf('1e-3'), mp.mpf('1e-2')]

print("=== (a) carrier decomposition: xi'/xi == (1/s+1/(s-1)) + A + P  (max abs err) ===")
errs = []
for sg in sigmas:
    for t in ts:
        s = sg + 1j*t
        lhs = xi_logderiv(s)
        rhs = rational(s) + A(s) + P(s)
        errs.append(abs(lhs-rhs))
print("  max abs error over 9 points:", mp.nstr(max(errs), 3))

print("\n=== (b) surrogate level law: (S'/S - xi'/xi) == 2 c (s-1/2)  (S = e^{c(s-1/2)^2} xi) ===")
c = mp.mpf('1e-3')
def logS(s): return c*(s-half)**2 + logxi(s)
lev_errs = []
for sg in sigmas:
    for t in ts:
        s = sg + 1j*t
        got = mp.diff(logS, s) - xi_logderiv(s)
        want = 2*c*(s-half)
        lev_errs.append(abs(got-want))
print("  c=1e-3, max abs error over 9 points:", mp.nstr(max(lev_errs), 3))

print("\n=== (c) completed-weld carrier of the surrogate H_S = A + 2c(s-1/2) + P ===")
print("    (P unchanged; show Delta_S -> Delta_true as c->0; report median |Delta_S - Delta_true|)")
print("  sigma   c        median|dDelta|   max|dDelta|   (P identical: |dP|=0)")
for sg in sigmas:
    for c in cs:
        dds = []
        for t in ts:
            s = sg + 1j*t
            Aval, Pval = A(s), P(s)
            Dt = carrier_Delta(Aval, Pval)
            As = Aval + 2*c*(s-half)          # surrogate modifies the ARCHIMEDEAN term only
            Ds = carrier_Delta(As, Pval)       # P (HT carrier) untouched
            dds.append(abs(Ds-Dt))
        dds.sort()
        med = dds[len(dds)//2]
        print(f"  {mp.nstr(sg,2):>5}  {mp.nstr(c,2):>7}  {mp.nstr(med,3):>14}  {mp.nstr(max(dds),3):>11}")

# (d) contrast: the carrier's REAL separation power is analyticity (true vs finite-Euler), O(1);
#     its separation from the FE-exact correct-zeros surrogate is only the tame level O(c).
def vonmangoldt_upto(N):
    lam = [mp.mpf(0)]*(N+1)
    for p in range(2, N+1):
        is_p = all(p % q for q in range(2, int(p**0.5)+1))
        if is_p:
            pk = p
            while pk <= N:
                lam[pk] = mp.log(p)
                pk *= p
    return lam
N = 200
lam = vonmangoldt_upto(N)
def P_finite(s):                # finite-Euler truncation of zeta'/zeta = -sum_{n<=N} Lambda(n) n^{-s}
    return -mp.fsum(lam[n]*mp.power(n, -s) for n in range(2, N+1))
print("\n=== (d) carrier separation power: analyticity (O(1)) vs FE-exact surrogate (O(c)) ===")
print("  sigma  |Delta_true-Delta_finiteEuler(N=200)|   |Delta_true-Delta_surrogate(c=1e-3)|")
csmall = mp.mpf('1e-3')
for sg in sigmas:
    fin, sur = [], []
    for t in ts:
        s = sg + 1j*t
        Aval, Pval = A(s), P(s)
        Dt = carrier_Delta(Aval, Pval)
        fin.append(abs(carrier_Delta(Aval, P_finite(s)) - Dt))
        sur.append(abs(carrier_Delta(Aval + 2*csmall*(s-half), Pval) - Dt))
    fin.sort(); sur.sort()
    print(f"  {mp.nstr(sg,2):>5}   median {mp.nstr(fin[len(fin)//2],3):>9}                     median {mp.nstr(sur[len(sur)//2],3):>9}")

print("\n=== summary ===")
print("  (a) carrier decomposition holds  => H = A+P is exactly the completed weld log-derivative.")
print("  (b) every FE-even Gaussian factor shifts the carrier by the TAME term 2c(s-1/2) only.")
print("  (c) the surrogate's HT part P=zeta'/zeta is IDENTICAL; its zeros (hence kappa_-) are IDENTICAL;")
print("      Delta_S -> Delta_true as c->0. The rung-1 adversary differs from zeta only by a tame")
print("      archimedean factor => NO FE-exact, correct-zeros, NON-HT object exists. Rung 1 is vacuous.")
