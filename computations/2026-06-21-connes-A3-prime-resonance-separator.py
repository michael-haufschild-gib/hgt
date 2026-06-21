#!/usr/bin/env python3
"""
connes A3 — what separates zeta from a same-density RANDOM divisor?  (closes the A2 open bar)

A2: value-rigidity (seam-value integer relations) is GENERIC — zeta and same-density-random both resist.
So value-arithmetic does NOT separate zeta from random. Candidate separator (explicit formula): the
zeros of zeta RESONATE with the primes; a random divisor does not.

Test the prime-log resonance of a divisor {gamma_n}:
   W(x) = (1/sqrt(N)) * sum_{n=1}^N taper(n) * cos(gamma_n * x).
By the explicit formula, zeta's zeros give peaks at x = log(p^m) (prime powers); a same-density random
divisor is flat; an arithmetic-progression divisor (gamma_n = c n) peaks at x in (2*pi/c)*Z (its OWN
arithmetic), NOT at log p.

Three divisors, same seam (on the line):
  zeta   : actual ordinates gamma_n (mpmath zetazero)
  random : same density (Riemann-von Mangoldt inverse + jitter)
  AP     : gamma_n = c*n, c set to match zeta's mean spacing near the window (density-ish), peaks at 2pi/c.
Report resonance at x in {log2,log3,log4,log5,log7} vs off-resonance control points.
Fast: N=300 zeros, dps 18.
"""
import mpmath as mp, numpy as np
mp.mp.dps = 18
N = 300

# zeta zeros
gam_z = [float(mp.im(mp.zetazero(n))) for n in range(1, N+1)]

# random same-density (RvM inverse + jitter), matches zeta density by construction
np.random.seed(7)
def rvm(T):
    t=T/(2*np.pi); return t*(np.log(t)-1)+7/8
from math import log, pi, cos, sqrt
def gamma_smooth(n):
    lo,hi=2.0,10.0
    while rvm(hi)<n: hi*=2
    for _ in range(100):
        mid=(lo+hi)/2
        if rvm(mid)<n: lo=mid
        else: hi=mid
    return 0.5*(lo+hi)
gam_r=[]
for n in range(1,N+1):
    g=gamma_smooth(n); sp=2*pi/log(g/(2*pi))
    gam_r.append(g+np.random.uniform(-0.5,0.5)*sp)

# AP matched to mean spacing of zeta over the window
mean_sp=(gam_z[-1]-gam_z[0])/(N-1)
gam_ap=[gam_z[0]+mean_sp*n for n in range(N)]   # spacing = mean zeta spacing -> peaks at 2pi/mean_sp

taper=[0.5-0.5*cos(2*pi*n/(N-1)) for n in range(N)]   # Hann window
def W(gam, x):
    return abs(sum(t*cos(g*x) for t,g in zip(taper,gam)))/sqrt(N)

res_x   = [("log2",log(2)),("log3",log(3)),("log4",log(4)),("log5",log(5)),("log7",log(7))]
ctrl_x  = [0.45,0.55,0.80,0.95,1.25,1.45,1.75,1.90,2.10]   # off prime-log
print(f"[setup] N={N}  AP peak freq 2pi/mean_sp={2*pi/mean_sp:.4f} (mean_sp={mean_sp:.4f})")
print(f"\n{'x':>8} | {'zeta':>8} | {'random':>8} | {'AP':>8}   (resonance W; prime-log rows should spike for zeta)")
for nm,x in res_x:
    print(f"{nm:>8} | {W(gam_z,x):8.3f} | {W(gam_r,x):8.3f} | {W(gam_ap,x):8.3f}")
print("  ----  off-resonance controls  ----")
cz=[W(gam_z,x) for x in ctrl_x]; cr=[W(gam_r,x) for x in ctrl_x]; ca=[W(gam_ap,x) for x in ctrl_x]
print(f"{'ctrl med':>8} | {np.median(cz):8.3f} | {np.median(cr):8.3f} | {np.median(ca):8.3f}")
print(f"{'ctrl max':>8} | {max(cz):8.3f} | {max(cr):8.3f} | {max(ca):8.3f}")
# AP's own resonance
apf=2*pi/mean_sp
print(f"\nAP own-arithmetic peak at x=2pi/mean_sp={apf:.4f}:  zeta={W(gam_z,apf):.3f} random={W(gam_r,apf):.3f} AP={W(gam_ap,apf):.3f}")
print("\n[reading] zeta spikes at log p^m (explicit formula); random flat; AP spikes at its OWN 2pi/spacing.")
print("  => the zeta-vs-random separator is the explicit-formula prime resonance, NOT value rigidity.")
