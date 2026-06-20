#!/usr/bin/env python3
# MACHINE workflow STEP 7 transfer: Ecalle BRIDGE-EQUATION experiment ([Delta_omega, d/dx]=0,
# i.e. large-order<->low-order CLOSURE) applied to HT asymptotic series.
# We do NOT transfer the constraint; we transfer the TEST PROCEDURE:
#   given divergent coeffs a_n: (1) read |A| (Borel-singularity / instanton action) from |a_n/a_{n+1}|;
#   (2) read the oscillation/sign-structure (real vs complex-conjugate Borel singularities);
#   (3) decode d_n = a_n * A^{n+b}/Gamma(n+b) -> should tend to a CONSTANT (single-instanton, bridge
#       closure) or admit a smooth 1/n expansion (resurgent). Non-smooth/non-converging => inert.
# Targets: Euler n! (control: resurgent, A=1, real single singularity),
#          Stirling log Gamma (Bernoulli, archimedean HT axis),
#          Stieltjes gamma_n of zeta (the s=1 pole / prime+zero axis).
import mpmath as mp
mp.mp.dps = 60

def ratio_table(a, name):
    # |a_n/a_{n+1}| and its Richardson-style limit estimate (should -> |A|, the instanton action)
    print(f"\n=== {name} : |a_n/a_{{n+1}}| (-> |A|) and sign(a_n) ===")
    r = []
    N = len(a)
    for n in range(N-1):
        if a[n+1] == 0:
            r.append(None); continue
        r.append(abs(a[n]/a[n+1]))
    # n*(|r_n|) grows like A*n if a_n~Gamma(n)/A^n; better: |a_n|^(1/n) -> 1/|A|
    # report |a_n|^{1/n} -> 1/|A| and r_n/n -> ... we print r_n and r_n/(n+1)
    for n in range(0, N-1, max(1,(N-1)//12)):
        sgn = '+' if mp.re(a[n])>0 else '-'
        rn = r[n]
        print(f"  n={n:3d}  |a_n/a_n+1|={mp.nstr(rn,8):>14}   r/(n+1)={mp.nstr(rn/(n+1),6):>12}   sign={sgn}")
    # |A| estimate from root test on last quarter
    q = a[3*N//4:]
    roots = [abs(x)**(mp.mpf(1)/(3*N//4 + i)) for i,x in enumerate(q) if x!=0]
    if roots:
        invA = roots[-1]
        print(f"  root-test |a_n|^(1/n) (last) = {mp.nstr(invA,8)}  => |A| ~ {mp.nstr(1/invA,8)}")
    return r

def closure_decode(a, A, b, name):
    # decode d_n = a_n * A^{n+b} / Gamma(n+b); single-instanton resurgent => d_n -> const (Stokes/2pi)
    # smoothness of d_n in 1/n = bridge closure; wild/divergent d_n = inert/non-resurgent for this A.
    print(f"\n--- {name}: decode with A={mp.nstr(A,6)}, b={b}  (d_n should stabilize if resurgent) ---")
    N=len(a)
    ds=[]
    for n in range(1,N):
        val = a[n]*A**(n+b)/mp.gamma(n+b)
        ds.append(val)
    for n in range(0,len(ds),max(1,len(ds)//10)):
        print(f"  n={n+1:3d}  d_n={mp.nstr(ds[n],8)}")
    # measure stabilization: relative spread of last 5
    tail=[abs(x) for x in ds[-6:] if x!=0]
    if len(tail)>=2:
        spread=(max(tail)-min(tail))/ (sum(tail)/len(tail))
        print(f"  tail relative spread (last~6): {mp.nstr(spread,5)}  (<~0.3 = stabilizing/resurgent)")
    return ds

# ---- Series 1: Euler  a_n = n!   (control: resurgent, single real Borel singularity A=1) ----
K=40
euler=[mp.factorial(n) for n in range(K)]
ratio_table(euler,"Euler n! (control, A=1)")
closure_decode(euler,mp.mpf(1),1,"Euler n!")

# ---- Series 2: Stirling log Gamma  c_k = B_{2k}/(2k(2k-1))  (archimedean HT axis) ----
# |B_{2k}| ~ 2 (2k)!/(2pi)^{2k}  => |A|=2pi, complex-conjugate pair at +-2pi i (sign alternates)
K2=44
stir=[mp.bernoulli(2*k)/(2*k*(2*k-1)) for k in range(1,K2)]
ratio_table(stir,"Stirling logGamma (Bernoulli, archimedean axis)")
# adjacent decode: |A|=2pi, the natural exponent b for c_k ~ |B_2k|/(2k)^2 ~ (2k-2)!/(2pi)^{2k}
closure_decode([abs(x) for x in stir], (2*mp.pi)**2, 0, "Stirling |c_k| (A=(2pi)^2 step-2)")

# ---- Series 3: Stieltjes gamma_n of zeta (s=1 pole expansion; prime+zero axis) ----
# zeta(s)=1/(s-1)+sum (-1)^n gamma_n (s-1)^n/n!   ; test resurgence of gamma_n
K3=40
print("\ncomputing Stieltjes gamma_n (mpmath)...")
gam=[mp.stieltjes(n) for n in range(K3)]
ratio_table(gam,"Stieltjes gamma_n of zeta (prime/zero axis)")
# gamma_n known to grow ~ (n/(2pi e... )) with OSCILLATION (Knessl-Coffey saddle) -> test single-A fail
closure_decode([abs(x) for x in gam], mp.mpf(1), 1, "|gamma_n| (trial A=1)")

print("\nDONE")
