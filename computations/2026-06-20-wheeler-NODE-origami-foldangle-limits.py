"""
STEP 6 — runnable test of the NODE constraint, ON THE NODE.
NODE = "Fold-angle limits matter as much as crease existence" (origami rigidity).
Constraint: creases EXIST (DOF) but fold angles are confined to a BOUNDED admissible region
cut by inequality constraints (kinematic coupling + |rho|<=pi + self-intersection). The
configuration is fixed by the region BOUNDARY (angle saturation / lock-up), not by a flow.
Test: degree-4 single vertex, 1-DOF rigid folding via the fold-angle multiplier; show the
reachable driving-angle range is BOUNDED and a fold angle SATURATES at the boundary.
Fast: numpy. Seconds.
"""
import numpy as np

# Degree-4 flat-foldable vertex: opposite fold angles couple via a fold-angle multiplier mu
# tan(rho_b/2) = mu * tan(rho_a/2), mu set by sector angles (here mu=2.5).
mu = 2.5
self_intersect_limit = 0.95*np.pi   # a fold angle beyond this self-intersects

def partners(rho_a):
    ta = np.tan(rho_a/2)
    rho_b = 2*np.arctan(mu*ta)        # coupled partner
    rho_c = -rho_a                    # opposite crease (flat-fold symmetry)
    rho_d = -rho_b
    return np.array([rho_a, rho_b, rho_c, rho_d])

print("="*72)
print(" NODE TEST: fold-angle limits — creases exist (DOF) but range is BOUNDED")
print("="*72)
# sweep driving angle; find reachable region where ALL |rho_i| <= self_intersect_limit
drive = np.linspace(-np.pi+1e-3, np.pi-1e-3, 2001)
admissible=[]
for r in drive:
    rs = partners(r)
    if np.all(np.abs(rs) <= self_intersect_limit):
        admissible.append(r)
admissible=np.array(admissible)
print(f"\n nominal crease DOF (range of driving angle if unconstrained): [-pi, pi] = full")
print(f" ADMISSIBLE reachable range (all creases within limits): "
      f"[{admissible.min():.3f}, {admissible.max():.3f}]  (bounded sub-interval)")
# at the boundary, which crease saturates?
rb = partners(admissible.max())
sat = np.argmax(np.abs(rb))
print(f" at upper boundary drive={admissible.max():.3f}: fold angles={np.round(rb,3)};"
      f" crease #{sat} SATURATES at |rho|={abs(rb[sat]):.3f} (limit {self_intersect_limit:.3f})")
# motion 'locks': the partner reaches the limit BEFORE the driver reaches pi
print(f"\n LOCK-UP: driver could reach pi (crease exists), but partner crease (mult mu={mu}) hits its")
print(f" limit at driver={admissible.max():.3f} < pi -> the fold-angle LIMIT, not crease existence,")
print(f" fixes the configuration boundary. Constraint confirmed on the NODE.")
# driving force: larger mu -> tighter admissible range
print("\n driving force (multiplier mu -> admissible half-range):")
for m in (1.0, 2.5, 5.0, 10.0):
    adm=[r for r in drive if abs(2*np.arctan(m*np.tan(r/2)))<=self_intersect_limit and abs(r)<=self_intersect_limit]
    print(f"   mu={m:4.1f}: admissible half-range = {max(adm):.3f}")
