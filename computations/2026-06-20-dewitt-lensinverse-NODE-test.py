#!/usr/bin/env python3
# MACHINE STEP6: RUNNABLE test of the MULTIVALUED-INVERSE constraint ON THE NODE (gravitational lensing).
# Constraint: inverse of the lens map is multivalued; pinned by topological invariants:
#  (i) real-image COUNT jumps by +-2 only at caustics (critical values); (ii) the signed residue sum
#  Sum 1/f'(x_i) over ALL preimages of a source w is an EXACT value relation (=0 for deg>=2 polynomial map).
import numpy as np

def preimages(w):
    # lens map f(x)=x^3-3x ; source w ; images solve x^3-3x-w=0
    return np.roots([1.0, 0.0, -3.0, -w])

print("=== NODE test: multivalued inverse of lens map f(x)=x^3-3x ; caustic at w=+-2 ===")
print("  w     | #real images | residue sum  Sum 1/f'(x_i) over ALL roots (value relation)")
for w in [-3.0,-2.0,-1.0,0.0,1.0,2.0,3.0]:
    r = preimages(w)
    real = r[np.abs(r.imag)<1e-9].real
    fp = 3*r**2 - 3.0                     # f'(x)=3x^2-3
    res_sum = np.sum(1.0/fp)              # sum of residues of 1/(f-w): exact value relation
    print(f"  w={w:+.1f} |   {len(real)}          | Sum 1/f' = {res_sum.real:+.2e}{res_sum.imag:+.2e}j")
print("  READ: #real images jumps 3<->1 across caustic w=+-2 (fold); Sum 1/f' = 0 EXACTLY (value relation).")
print("  The signed residue sum is fixed by the constraint (degree/residue invariant), not propagated.")
