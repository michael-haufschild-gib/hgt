import GaloisForLFunctions.HTGeometry.AlternatingChordLaw

/-!
# The Suzuki resolvent chord as one decomposable blade

Two shifted resolvent states of a common source are `u_beta = A v - alpha • v` and
`u_alpha = A v - beta • v`, where `v` is the product-resolvent state.  In the exterior square their
wedge is the *fixed* blade `v ∧ A v` rescaled by the shift gap, and after homogenizing by the
affine Neumann channel the same law holds in `V × R` with the homogeneous coordinate carried by the
second slot.  So the two-shift Euler--Gamma motion and the affine Neumann channel are components of
one decomposable blade rather than independent corrections.
-/

open scoped ExteriorAlgebra

namespace RHTower

open GaloisForLFunctions.HTGeometry

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Fixed Plücker blade of a resolvent chord.**  For the product-resolvent state `v` the two
shifted states wedge to the fixed blade `v ∧ A v`, rescaled by the shift gap. -/
theorem suzukiResolventBlade_chord (A : V →ₗ[R] V) (α β : R) (v : V) :
    exteriorPower.ιMulti R 2 ![A v - α • v, A v - β • v] =
      (β - α) • exteriorPower.ιMulti R 2 ![v, A v] :=
  exteriorPair_chord α β v (A v)

/-- The two shifted homogeneous states differ from the homogeneous pair `((v,0), (A v,1))` in the
same way. -/
theorem suzukiHomogeneousState_eq (A : V →ₗ[R] V) (α : R) (v : V) :
    ((A v - α • v, (1 : R)) : V × R) = (A v, (1 : R)) - α • (v, (0 : R)) := by
  simp

/-- **Homogeneous blade law.**  Adjoining the affine Neumann channel as a homogeneous coordinate,
the chord of the two shifted resolvent states is the fixed homogeneous blade
`(v,0) ∧ (A v,1)` rescaled by the shift gap.  Its `V ∧ V` part is the Euler--Gamma projective
curvature and its `V ∧ F` part is the affine Neumann channel. -/
theorem suzukiHomogeneousResolventBlade_chord (A : V →ₗ[R] V) (α β : R) (v : V) :
    exteriorPower.ιMulti R 2
        ![((A v - α • v, (1 : R)) : V × R), ((A v - β • v, (1 : R)) : V × R)] =
      (β - α) • exteriorPower.ιMulti R 2
        ![((v, (0 : R)) : V × R), ((A v, (1 : R)) : V × R)] := by
  rw [suzukiHomogeneousState_eq A α v, suzukiHomogeneousState_eq A β v]
  exact exteriorPair_chord α β ((v, (0 : R)) : V × R) ((A v, (1 : R)) : V × R)

end RHTower
