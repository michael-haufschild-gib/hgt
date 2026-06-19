#!/usr/bin/env python3
"""
Gap-margin probe (Wheeler, 2026-06-19): the well-conditioned, direct read on (GD).

The RH-bearing quantity is the section root gaps: rho_{l+1}-rho_l = Delta_l - DeltaEps_l, so the
relative min gap = 1 - R_d(t) where R_d = max_l |DeltaEps_l|/Delta_l (the gap-difference ratio of (GD)).
Compute the ACTUAL roots of the full Jensen section J_d(X;t) of Xi (real zeta), via polyroots
(better-conditioned than the power-sum Hankel), and report:
  - whether all roots real (hyperbolic) -- a complex pair = RH-violation in the section,
  - the relative min gap  g_d(t) = min_l(rho_{l+1}-rho_l) / mean_l(rho_{l+1}-rho_l),
  - min over t of g_d(t)  (the worst/closest approach), and its d-trend.

If min_t g_d stays bounded below as d grows -> margin OK (GD has room); if -> 0 -> no-margin closing.
Bounded: d in 2..DMAX, t-grid NT points.
"""
import mpmath as mp
mp.mp.dps = 30
DMAX = 8
T0, T1, NT = 0.5, 80.0, 161
CD_GUARD = mp.mpf('1e-18')

def xi(s): return mp.mpf('0.5')*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)
def Xi(z): return xi(mp.mpf('0.5')+1j*z)
def jcoef(t,d):
    c=[mp.re(x) for x in mp.taylor(Xi,mp.mpf(t),d)]   # Xi^{(j)}(t)/j!
    return [mp.binomial(d,j)*c[j] for j in range(d+1)]   # ascending: a_0 + a_1 X + ... + a_d X^d

tg=[T0+(T1-T0)*k/(NT-1) for k in range(NT)]
print(f"# gap-margin probe dps={mp.mp.dps} DMAX={DMAX} t in [{T0},{T1}] NT={NT}")
for d in range(2,DMAX+1):
    worst_g=mp.mpf('1e9'); t_worst=None; ncomplex=0; nused=0; minrelgap_list=[]
    for t in tg:
        a=jcoef(t,d)
        if abs(a[d])<CD_GUARD*(abs(a[0])+1): continue
        nused+=1
        coeffs=[a[d-k] for k in range(d+1)]            # polyroots wants descending: a_d ... a_0
        try:
            roots=mp.polyroots([mp.mpf(c) for c in coeffs], maxsteps=200, extraprec=60)
        except Exception:
            continue
        ims=[abs(mp.im(r)) for r in roots]
        reps=sorted([mp.re(r) for r in roots])
        scale=max(abs(reps[0]),abs(reps[-1]),mp.mpf(1))
        if max(ims) > mp.mpf('1e-9')*scale:            # a genuinely complex root => collision/off-axis
            ncomplex+=1; continue
        gaps=[reps[i+1]-reps[i] for i in range(d-1)]
        if not gaps: continue
        mg=min(gaps); meang=sum(gaps)/len(gaps)
        relg=mg/meang
        minrelgap_list.append(relg)
        if relg<worst_g: worst_g=relg; t_worst=t
    avg_relg = (sum(minrelgap_list)/len(minrelgap_list)) if minrelgap_list else mp.mpf('nan')
    print(f"d={d}: min_t rel-min-gap={mp.nstr(worst_g,5)} @t={mp.nstr(t_worst,5)} | "
          f"mean_t rel-min-gap={mp.nstr(avg_relg,4)} | complex-root t's={ncomplex}/{nused}")
print("# done")
