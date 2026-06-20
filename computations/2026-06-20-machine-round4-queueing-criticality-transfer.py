#!/usr/bin/env python3
# THE MACHINE (corrected protocol) — Round 4.
# NODE (rng seed 2717109681234817563, one node): QUEUEING-AT-BORDERS. Constraint-move: degenerate-case.
# Worked ONLY inside queueing: a single-server queue has a genuine (normalizable) stationary state only
# below critical load rho<1; at the degenerate point rho->1 the mean diverges and the generating-function
# pole z*=1/rho migrates onto the unit circle. CONSTRAINT = stability/normalizability boundary.
# REMOTE EXPERIMENT (the procedure, not the analogy): divergence_exponent(f, dist_to_critical) =
#   slope of log f vs log(dist) as a control -> its degenerate value. For M/M/1: L(rho)=rho/(1-rho),
#   expect exponent 1 (Kingman/geometric class).
# TRANSFER step: run the SAME exponent-extractor on the PROBLEM'S object with s as the load parameter:
#   zeta(s), Hurwitz zeta(s,a), Dirichlet-beta(s) [=L(s,chi_4)], as s->1+ (the convergence/stability
#   boundary of sum n^{-s}). Record data. Classify honestly (dead-end / boundary-marker / win).
import mpmath as mp
mp.mp.dps = 40

def divergence_exponent(f, dists):
    # fit log|f(crit+d)| ~ -gamma*log d  -> return gamma (the blow-up exponent). gamma~0 => no divergence.
    xs = [mp.log(d) for d in dists]
    ys = [mp.log(abs(f(d))) for d in dists]
    n = len(xs); sx = mp.fsum(xs); sy = mp.fsum(ys)
    sxx = mp.fsum(x*x for x in xs); sxy = mp.fsum(xs[i]*ys[i] for i in range(n))
    slope = (n*sxy - sx*sy)/(n*sxx - sx*sx)
    return -slope   # f ~ d^{slope} = d^{-gamma}

dists = [mp.mpf(10)**-k for k in range(2, 8)]   # approach the critical boundary

# --- PART A: remote (queueing). M/M/1 mean queue length L(rho)=rho/(1-rho), control = 1-rho -> 0 ---
def L_mm1(d):  # d = 1-rho ; rho = 1-d
    rho = 1 - d
    return rho/(1-rho)
gamma_queue = divergence_exponent(L_mm1, dists)
z_star = lambda rho: 1/rho
print("=== PART A: QUEUEING (remote) ===")
print(f"  M/M/1 mean-blowup exponent gamma = {float(gamma_queue):.6f}  (expect 1; geometric/Kingman class)")
print(f"  GF pole z*=1/rho at rho=0.99 -> {float(z_star(0.99)):.5f} (->1 = pole hits unit circle at criticality)")

# --- PART B: TRANSFER. Same procedure, s = load; critical boundary s=1 (abscissa of convergence) ---
def beta(s):  # Dirichlet beta = L(s, chi_4) ; chi_4 non-principal mod 4
    return mp.mpf(4)**(-s) * (mp.zeta(s, mp.mpf(1)/4) - mp.zeta(s, mp.mpf(3)/4))
objs = [
 ("zeta(s)",            lambda d: mp.zeta(1+d)),
 ("Hurwitz zeta(s,0.3)",lambda d: mp.zeta(1+d, mp.mpf('0.3'))),
 ("Hurwitz zeta(s,2.7)",lambda d: mp.zeta(1+d, mp.mpf('2.7'))),
 ("Dirichlet beta(s)",  lambda d: beta(1+d)),
]
print("\n=== PART B: TRANSFER to the problem's object (s->1+, same exponent-extractor) ===")
print(f"{'object':22s} {'exponent gamma':>16s}   queueing class")
rows=[]
for name, f in objs:
    g = divergence_exponent(f, dists)
    cls = "CRITICAL (pole, gamma~1)" if abs(g-1) < 0.05 else ("SUBCRITICAL (gamma~0)" if abs(g) < 0.05 else f"other gamma={float(g):.3f}")
    rows.append((name, g, cls))
    print(f"{name:22s} {float(g):16.6f}   {cls}")

# residue check (sharpen: for a simple pole, (s-1)*f -> residue) ; universality across a
print("\n  residue at s=1 (=(s-1)*f as s->1+):")
for name, f in objs:
    r = (mp.mpf(10)**-7) * f(mp.mpf(10)**-7)
    print(f"    {name:22s} residue ~ {float(r):.6f}")

print("\n=== CLASSIFY (self-curated) ===")
print("  Transferred procedure partitions Dirichlet/HT objects by QUEUEING CRITICALITY:")
print("  - zeta, Hurwitz-zeta = M/M/1 universality class (simple pole at s=1, gamma=1, residue 1,")
print("    a-INDEPENDENT = universal critical exponent). The arithmetic regime (critical strip s<1)")
print("    is the SUPERCRITICAL/continued zone: sum n^{-s} diverges, object exists only by continuation,")
print("    exactly a queue continued past stability rho>1.")
print("  - Dirichlet L (non-principal chi) = SUBCRITICAL (entire, gamma=0): character cancellation keeps")
print("    the constraint saturated with slack -> never reaches criticality.")
print("  Underlying facts (pole order/residue, L entire) are CLASSICAL -> reduces-to-known => BOUNDARY-MARKER,")
print("  NOT a win. The cumulative datum = the queueing-universality-class partition + 'critical strip =")
print("  supercritical continued-queue' framing of where RH lives.")
