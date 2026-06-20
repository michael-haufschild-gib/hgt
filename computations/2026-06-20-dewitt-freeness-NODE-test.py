#!/usr/bin/env python3
# MACHINE STEP6: RUNNABLE test of the NODE (free probability): vanishing mixed moments do NOT imply freeness;
# a FINITE moment check is necessary-not-sufficient. Freeness = ALL alternating centered moments vanish.
import numpy as np
rng = np.random.default_rng(11)
N = 400
def tr(M): return np.trace(M).real/N
def center(M): return M - tr(M)*np.eye(N)
def norm2(M):  # normalize to unit second moment
    return M/np.sqrt(tr(center(M)@center(M)))

# free pair: two INDEPENDENT GUE (asymptotically FREE)
def gue():
    A=(rng.normal(size=(N,N))+1j*rng.normal(size=(N,N)))/np.sqrt(2); return (A+A.conj().T)/2
a_f=center(norm2(gue())); b_f=center(norm2(gue()))
# classical/commuting pair: two INDEPENDENT diagonal (commute) -> classically independent, NOT free
a_c=center(norm2(np.diag(rng.normal(size=N)))); b_c=center(norm2(np.diag(rng.normal(size=N))))

def alt_moments(a,b):
    return {
        "tau(ab)        order2": tr(a@b),
        "tau(abab)      order4": tr(a@b@a@b),
        "tau(aabb) (non-alt)  ": tr(a@a@b@b),
    }
print("=== NODE test: finite mixed-moment check is NOT sufficient for freeness ===")
print("  FREE pair (independent GUE):")
for k,v in alt_moments(a_f,b_f).items(): print(f"    {k} = {v:+.5f}")
print("  CLASSICAL/commuting pair (independent diagonal):")
for k,v in alt_moments(a_c,b_c).items(): print(f"    {k} = {v:+.5f}")
print("\n  READ: order-2 tau(ab)=0 for BOTH (passes finite check). The ALTERNATING order-4 tau(abab)")
print("  is ~0 for the FREE pair but NONZERO (=tau(a^2)tau(b^2)) for the classical pair => finite check")
print("  insufficient; freeness needs the FULL all-orders alternating-centered constraint.")
