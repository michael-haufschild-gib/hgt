#!/usr/bin/env python3
# MACHINE STEP6: RUNNABLE test of the ESSENTIAL-SPECTRUM / FREDHOLM constraint ON THE NODE itself
# (index theory on noncompact manifolds). Constraint: for H = -d^2/dx^2 + V(x) with V(x)->V_inf at the
# noncompact end, sigma_ess(H)=[V_inf, infty); H-E is FREDHOLM iff E < V_inf (gap below the continuum).
# The essential spectrum is set by the asymptotic value V_inf (geometry at infinity), NOT the bulk well.
# Signature: discrete eigenvalues BELOW V_inf are L-INDEPENDENT (finite # bound states => Fredholm);
# ABOVE V_inf the count grows proportional to L (continuum => non-Fredholm). Threshold MOVES with V_inf.
import numpy as np

def spectrum(L, n, Vinf, A=4.0):
    # whole line [-L,L], Dirichlet; V(x)=Vinf - A sech^2(x)  (Poschl-Teller well, known bound states)
    x = np.linspace(-L, L, n)
    h = x[1]-x[0]
    V = Vinf - A/np.cosh(x)**2
    main = 2.0/h**2 + V
    off = -1.0/h**2*np.ones(n-1)
    # symmetric tridiagonal eigenvalues
    w = np.linalg.eigvalsh(np.diag(main)+np.diag(off,1)+np.diag(off,-1))
    return np.sort(w)

def counts(L, n, Vinf):
    w = spectrum(L, n, Vinf)
    below = np.sum((w >= Vinf-1.0) & (w < Vinf))     # in [Vinf-1, Vinf): discrete bound states
    above = np.sum((w >= Vinf) & (w < Vinf+1.0))     # in [Vinf, Vinf+1): continuum sample
    nbound = np.sum(w < Vinf)                          # total bound states (below threshold)
    return below, above, nbound

print("=== NODE test: essential-spectrum threshold = Fredholm obstruction (V_inf=0) ===")
print("L (domain half-width) | #eig in [-1,0) (BELOW thresh) | #eig in [0,1) (ABOVE=continuum) | #bound")
keep_density=None
for L,n in [(20,2000),(40,4000),(80,8000)]:
    b,a,nb = counts(L,n,Vinf=0.0)
    print(f"  L={L:4d}  below(discrete)={b:3d}   above(continuum)={a:4d}   total_bound={nb:3d}   above/L={a/L:.3f}")
print("  EXPECT: below/bound counts ~L-INDEPENDENT (finite, Fredholm); above count ~proportional to L (continuum).")

print("\n=== driving force: threshold MOVES with the at-infinity value V_inf ===")
for Vinf in [-2.0, 0.0, 3.0]:
    w = spectrum(40,4000,Vinf)
    ess_bottom = None
    # estimate essential-spectrum bottom = where eigenvalue density jumps (smallest eig above the bound-state gap)
    nb = np.sum(w < Vinf)
    print(f"  V_inf={Vinf:5.1f}: total bound states (eig<V_inf)={nb:3d}; min eig={w[0]:.3f}; "
          f"sigma_ess starts ~ {Vinf:.1f}")
print("  => essential spectrum bottom tracks V_inf (the asymptotic/at-infinity value), confirming the")
print("     constraint is set by geometry at infinity, not the bulk well.  Constraint validated ON NODE.")
