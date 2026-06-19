#!/usr/bin/env python3
# Weyl-law test for: moonshot-arithmetic-bulk-hyperbolic.md.
# If zeros {1/4+gamma^2} are a d-dim manifold Laplacian spectrum: N(lambda<L) ~ C*L^{d/2}.
# Actual zero counting (Riemann-von Mangoldt): N(gamma<T) ~ (T/2pi)log(T/2pi) - T/2pi.
# Measured effective d/2 = log N / log(lambda), lambda ~ T^2.  Result: d/2 -> 1/2, i.e. d -> 1
# (Berry-Keating xp / 1D), NOT d=2 (surface) or d=3 (3-manifold). Local, sub-second, no runpod.
import mpmath as mp
mp.mp.dps = 20

print("T (=gamma)    N_RvM(T)        d/2 = log N / log(T^2)     d")
for T in [50, 200, 1000, 5000, 50000]:
    Tm = mp.mpf(T)
    N = Tm/(2*mp.pi)*mp.log(Tm/(2*mp.pi)) - Tm/(2*mp.pi) + mp.mpf(7)/8
    lam = Tm**2
    d2 = mp.log(N)/mp.log(lam)
    print("  T=%-7d N=%-12s d/2=%s  d=%s" % (T, mp.nstr(N, 7), mp.nstr(d2, 5), mp.nstr(2*d2, 5)))
print()
print("d/2 -> 1/2 (d -> 1): zeros count like a 1D system (Berry-Keating xp / quantum graph),")
print("NOT a 2D surface (N~lambda) or 3D manifold (N~lambda^{3/2}). Finite-manifold bulk REFUTED;")
print("refined to 1D-xp or non-compact adelic (Connes) bulk.")
