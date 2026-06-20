#!/usr/bin/env python3
# THE MACHINE (corrected protocol) — Round 5.
# WIDE pick (codex+rng): #20 Ceramic glazing. NODE (codex+rng): #4 Gerstley borate (a natural borate flux).
# Codex-listed constraints (worked IN-NODE). Two with the sharpest runnable PROCEDURE:
#   #9 "melts early, can SEAL gases before burnout finishes": a fast process (melt/seal) prevents a slower
#       process (degas/burnout) from completing -> structure TRAPPED. Procedure = two completion-processes +
#       a control parameter -> find where their completion ORDER inverts, and what gets trapped.
#   #14 "fritted boron sources melt cleaner/more consistent": pre-stabilizing a raw flux extends its clean
#       working range. Procedure = compare a raw vs a pre-stabilized form's working range.
# TRANSFER (procedures, not analogy) to the PROBLEM'S object (zeta):
#   A = "burnout/multiplicative buildup" = partial Euler product E_P(s)=prod_{p<=P}(1-p^-s)^-1.
#   "fritted" form = alternating Dirichlet eta A_N(s)=sum_{n<=N}(-1)^{n-1} n^-s, eta=(1-2^{1-s}) zeta.
#   control = sigma=Re(s). MEASURE the SEALING curve: smallest sigma each process still "completes"
#   (tracks zeta within tol) -> where does the order invert, what is trapped (the critical strip / zeros)?
import mpmath as mp
mp.mp.dps = 30

def primes_upto(P):
    sieve=[True]*(P+1); sieve[0:2]=[False,False]
    for i in range(2,int(P**0.5)+1):
        if sieve[i]:
            for j in range(i*i,P+1,i): sieve[j]=False
    return [i for i in range(2,P+1) if sieve[i]]

def euler_partial(s, P):
    pr=primes_upto(P); v=mp.mpf(1)
    for p in pr: v*= 1/(1-mp.mpf(p)**(-s))
    return v
def eta_partial(s, N):
    return mp.fsum(((-1)**(n-1))*mp.mpf(n)**(-s) for n in range(1,N+1))
def eta_to_zeta(etaval, s):
    f=(1-mp.mpf(2)**(1-s))
    return etaval/f if f!=0 else mp.nan

sigmas=[mp.mpf(x) for x in ['2.0','1.5','1.2','1.05','0.9','0.7','0.5','0.3']]
P=5000; N=20000
print(f"P(euler primes<= {P}), N(eta terms)= {N}; rel-err vs true zeta(sigma):")
print(f"{'sigma':>6}  {'EulerProd relerr':>18}  {'eta(fritted) relerr':>20}")
seal_euler=None; seal_eta=None
for sg in sigmas:
    s=sg  # real s
    zt=mp.zeta(s)
    try:
        ep=euler_partial(s,P); ee=abs(ep-zt)/abs(zt)
    except Exception: ee=mp.nan
    try:
        et=eta_to_zeta(eta_partial(s,N),s); en=abs(et-zt)/abs(zt)
    except Exception: en=mp.nan
    print(f"{float(sg):6.2f}  {float(ee):18.3e}  {float(en):20.3e}")
    if (ee==ee) and ee<mp.mpf('1e-3'): seal_euler=sg
    if (en==en) and en<mp.mpf('1e-3'): seal_eta=sg
print(f"\nEuler product 'completes' (relerr<1e-3) down to sigma>= {float(seal_euler) if seal_euler else 'none'}")
print(f"eta (fritted) 'completes' down to sigma>= {float(seal_eta) if seal_eta else 'none'}")
print("\n=== self-curate (steps 6-7) ===")
print("Surprising? Does it show a rule I did NOT already know?")
print("  Euler product seals at sigma->1 (abscissa of abs convergence); eta survives to sigma->0 (the strip).")
print("  These are the CLASSICAL abscissae; 'fritting=series-acceleration' is a known reframing. The trapped")
print("  structure (zeros in 0<sigma<1) sealed off from the multiplicative process = known intuition.")
print("  => NOT surprising, NO new rule => DEAD END (the expected majority). Bank as dead-end; do not manufacture.")
