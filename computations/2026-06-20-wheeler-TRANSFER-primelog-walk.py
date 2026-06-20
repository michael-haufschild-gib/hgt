"""
STEP 7 (corrected workflow) — STRUCTURAL transfer of the NODE script by analogy/metaphor,
minimal changes. The NODE script:
    state = circle R/Z ; walk step = +-alpha ; averaging op M e_k = cos(2 pi k alpha) ;
    obstruction = unimodular eigenvalue at k!=0 (=> alpha rational => periodic orbit).
SAME SKELETON. The ONLY mutation (by metaphor): the single rotation 'alpha' becomes the
hypertranscendental object's natural translations -- the weld's prime-shifts {sigma_p},
"primes are the rotations": step = +- log p. Circle circumference L. Everything else kept.

Metaphor transferred (NOT the constraint): "a translation walk equidistributes unless its
step resonates into a periodic orbit." Here the steps are {log p}, Q-independent (unique
factorisation), so the obstruction cannot be a rational resonance -- it must hide in the
SPECTRUM:  M e_k = mean_p cos(2 pi k log p / L)  =  Re of the prime-zeta sum sampled.
We run the IDENTICAL obstruction test and LOOK (step 8), no pre-judging.
Fast: numpy, < 1 s.
"""
import numpy as np
from sympy import primerange
rng = np.random.default_rng(12345)

K = 60
ks = np.arange(1, K+1)

# --- the HT object's natural steps: prime logs (was: single scalar alpha) ---
primes = np.array(list(primerange(2, 2000)))   # ~300 primes
logs = np.log(primes)
L = logs.max() * 1.0                            # circle circumference (phase normalisation)
a_steps = logs / L                              # steps on R/Z  (analog of alpha)

def spectral_obstruction():
    # M e_k = mean_p cos(2 pi k a_p)   (was cos(2 pi k alpha); step-set swapped, form identical)
    vals = np.array([np.mean(np.cos(2*np.pi*k*a_steps)) for k in ks])
    absvals = np.abs(vals)
    kmax = int(ks[np.argmax(absvals)])
    return vals, float(np.max(absvals)), kmax

def empirical_discrepancy(nsteps=400000, nbins=50):
    # walk: +- random prime-log  (was +- alpha). Same cumulative walk on the circle.
    steps = rng.choice(a_steps, size=nsteps) * rng.choice([1.0, -1.0], size=nsteps)
    pos = np.cumsum(steps) % 1.0
    hist, _ = np.histogram(pos, bins=nbins, range=(0,1))
    p = hist / hist.sum()
    return 0.5*np.sum(np.abs(p - 1.0/nbins)), int(np.count_nonzero(hist))

print("="*78)
print(" TRANSFERRED TEST: prime-log walk on R/Z (HT object's {sigma_p} as the rotation)")
print("="*78)
vals, top, kmax = spectral_obstruction()
tv, occ = empirical_discrepancy()
obstruction = top > 1 - 1e-6
print(f"\n spectral: max_{{k>=1}} |mean_p cos(2pi k log p / L)| = {top:.6f} at k={kmax}")
print(f"   -> {'UNIMODULAR => PERIODIC OBSTRUCTION' if obstruction else 'gap => NO periodic obstruction (Q-indep of log p)'}")
print(f" empirical prime-log walk (400k steps): TV from uniform = {tv:.4f}, bins occ = {occ}/50"
      f"  -> {'TRAPPED' if tv>0.3 else 'EQUIDISTRIBUTED'}")

# --- LOOK at the SPECTRUM (where the obstruction had to hide) ---
print("\n SPECTRUM of the averaging operator across k = the prime-zeta sample:")
print(" k :  M_k = mean_p cos(2pi k log p / L)   (this is Re of a prime-zeta-type sum)")
for k in [1,2,3,5,8,13,21,34,55]:
    mk = np.mean(np.cos(2*np.pi*k*a_steps))
    print(f"   k={k:3d}:  M_k = {mk:+.4f}")

# near-1 accumulation? compare to a control: random Q-independent steps (no arithmetic)
ctrl = rng.uniform(0.05, 1.0, size=len(a_steps))
ctrl_top = max(abs(np.mean(np.cos(2*np.pi*k*ctrl))) for k in ks)
print(f"\n CONTROL (random Q-indep steps, no primes): max_k |M_k| = {ctrl_top:.4f}")
print(f" PRIME steps                              : max_k |M_k| = {top:.4f}  at k={kmax}")
print("\n STEP 8 -> read off: is the prime spectrum SPECIAL vs a generic Q-indep step set?")
