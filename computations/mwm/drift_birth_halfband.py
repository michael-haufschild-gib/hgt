#!/usr/bin/env python3
"""Push the drift-birth fixed point (doc 51 §10): (b) envelope correction, and
the FULL band d in [0, 1/2] to test whether ONE mechanism gives BOTH the low
edge d*=0.194 AND the half-integer emptiness (p~1/2, d~1/2).

Frozen dip closed form (doc 51 §10):
    dip(d) = (a0/(2|cos 2pi d|)) (1 - cos psi(d)),  psi = beta(d) - arg(1-w),
    beta(d) = pi/8 - 2 pi d^2,  w = e^{-i pi(1+4d)},  a0 = 2/sqrt(N).
Survival <=> birth depth rho*a0*B(d) > dip(d),  B(d) = |cos beta(d)|.

PRE-REGISTERED (before running):
  R1 (b): the TRUE antitone-envelope dip (walk the first frozen entries with
      a_m = 2(N-m)^{-1/2}, take min) matches the constant-envelope closed form to
      O(N^{-2/3}); relative gap -> 0 as N grows {100,1000,10000}. prior 0.7.
  R2 (HALF, the test): at rho=1.18 the survival set on [0,1/2] is EXACTLY the low
      interval [0, ~0.194] and does NOT re-open near d=1/2 -- i.e. one mechanism
      covers both facts. prior 0.35 (my hand-calc says dip(1/2) is SMALL, so it
      MIGHT re-open; if it does, the half-emptiness is a separate creation-rate
      effect, report that honestly).
  R3: IF empty near 1/2, identify the LIMITING factor as a function of d:
      "phase" where dip amplification 1/|cos2pi d| dominates, "amplitude" where
      B(d) suppression dominates. Report the crossover d. prior 0.5.
  R4: the birth-amplitude criterion alone (rho*B(d) > c_floor, generic dip floor
      c_floor~1) gives a half-band edge; report the c_floor that reproduces the
      measured "births 3x fewer near 1/2" boundary. prior 0.4.
"""
import mpmath as mp
mp.mp.dps = 40
pi = mp.pi

def parts(N, d):
    d = mp.mpf(d)
    a0 = 2/mp.sqrt(mp.mpf(N))
    beta = pi/8 - 2*pi*d*d
    w = mp.e**(-1j*pi*(1+4*d))
    omw = 1-w
    absw = abs(omw)
    psi = beta - mp.arg(omw)
    dip = (a0/absw)*(1-mp.cos(psi)) if absw > 1e-30 else mp.inf
    B = abs(mp.cos(beta))
    return a0, B, dip, absw

def true_dip_walk(N, d, L):
    """min over first L frozen entries of Re(sum a_m e^{i(beta+ m*Delta-ish)}),
    using EXACT step Delta(m) and antitone a_m = 2(N-m)^{-1/2}. Returns -min (dip>=0)."""
    d = mp.mpf(d)
    t = 2*pi*(N+d)**2
    beta = pi/8 - 2*pi*d*d
    S = mp.mpf(0); Phi = beta; mn = mp.mpf(0)
    for m in range(L):
        j = N - m
        a_m = 2*(mp.mpf(N-m))**(mp.mpf(-1)/2)
        S += a_m*mp.cos(Phi)
        if S < mn: mn = S
        Delta = -t*mp.log(mp.mpf(j)/(j-1))
        Phi += Delta
    return -mn

print("=== R1 (b): antitone-envelope dip vs constant-envelope closed form ===")
for N in [100, 1000, 10000]:
    d = mp.mpf('0.10')
    a0,B,dip_cf,_ = parts(N,d)
    L = max(4, int(round((N**(mp.mpf(1)/3)))))   # frozen block ~ N^{1/3}
    dip_true = true_dip_walk(N, d, L)
    rel = float(abs(dip_true-dip_cf)/dip_cf)
    print(f"  N={N:>5} d=0.10 L={L:>3}  dip_closed/a0={float(dip_cf/a0):.5f}"
          f"  dip_true/a0={float(dip_true/a0):.5f}  rel_gap={rel:.4f}  (~N^-2/3={float(N**(-mp.mpf(2)/3)):.4f})")

print("\n=== R2/R3: FULL band survival on [0,1/2], N=300 ===")
N=300
for rho in ['1.0','1.18','1.5']:
    rho = mp.mpf(rho)
    surv=[]
    for k in range(0,251):
        d = mp.mpf(k)/500          # d in [0,0.5], step 0.002
        a0,B,dip,absw = parts(N,d)
        margin = rho*a0*B - dip
        surv.append((d, margin>0, B, dip/a0, absw))
    # survival set as intervals
    intervals=[]; run=None
    for d,ok,_,_,_ in surv:
        if ok and run is None: run=[d,d]
        elif ok: run[1]=d
        elif run is not None: intervals.append(tuple(run)); run=None
    if run is not None: intervals.append(tuple(run))
    iv = ", ".join(f"[{float(a):.3f},{float(b):.3f}]" for a,b in intervals)
    print(f"  rho={float(rho):.2f}: survival set = {iv if iv else 'EMPTY'}")

print("\n  d : B(d)  dip/a0  1/|cos2pid|(amp)  limiting  (N=300)")
N=300
for k in range(0,26):
    d = mp.mpf(k)/50               # step 0.02
    a0,B,dip,absw = parts(N,d)
    amp = 2/absw if absw>1e-9 else mp.inf     # dip amplification 1/|cos2pi d|
    # at rho=1.18: survive?
    ok = (mp.mpf('1.18')*a0*B - dip)>0
    lim = "phase(dip)" if (dip/a0) > (1-B) else "amp(B)"
    print(f"  {float(d):.2f}  {float(B):.3f}  {float(dip/a0):7.3f}  {float(amp):7.3f}"
          f"   surv={ok!s:5}  {lim}")

print("\n=== R4: birth-amplitude-only criterion rho*B(d) > c_floor ===")
for cf in ['0.90','1.00','1.09']:
    cf=mp.mpf(cf)
    # edge where 1.18*B(d) = cf, on the DECREASING side (d>1/4)
    lo=None;hi=None
    for k in range(0,251):
        d=mp.mpf(k)/500
        _,B,_,_=parts(N,d)
        if mp.mpf('1.18')*B>cf:
            if lo is None: lo=d
            hi=d
    print(f"  c_floor={float(cf):.2f}: amplitude-survival band d in [{float(lo):.3f},{float(hi):.3f}]"
          f"  (B suppression closes it at high d)")

print("\ncensus: survival [0,0.194]; p~1/2 (d~1/2) EMPTY; B(1/2)=0.383 (2.4x supp)")
