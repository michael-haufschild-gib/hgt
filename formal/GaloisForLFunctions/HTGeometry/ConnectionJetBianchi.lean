import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

/-!
# Differential Bianchi algebra of a connection two-jet

The curvature and its first derivative are expanded from connection values and
first/second coordinate derivatives. Commuting coordinate second derivatives
force the cyclic covariant exterior derivative to vanish. Multiplication remains
noncommutative throughout, so the result applies to connection matrices.
-/

namespace GaloisForLFunctions.HTGeometry.ConnectionBianchi
variable {ι R : Type*} [Ring R]

/-- Curvature forced by connection values and first coordinate derivatives. -/
def curvature (A : ι → R) (D : ι → ι → R) (i j : ι) : R :=
  D i j - D j i + A i * A j - A j * A i

/-- Actual product-rule expression for the coordinate derivative of curvature. -/
def curvaturePartial (A : ι → R) (D : ι → ι → R) (H : ι → ι → ι → R)
    (k i j : ι) : R :=
  H k i j - H k j i + D k i * A j + A i * D k j - D k j * A i - A j * D k i

/-- Connection on endomorphisms applied to the curvature two-form. -/
def covariantExteriorPartial (A : ι → R) (D : ι → ι → R) (H : ι → ι → ι → R)
    (k i j : ι) : R :=
  curvaturePartial A D H k i j + A k * curvature A D i j - curvature A D i j * A k

/-- Curvature is alternating in the two coordinate-form indices. -/
theorem curvature_skew (A : ι → R) (D : ι → ι → R) (i j : ι) :
    curvature A D i j = -curvature A D j i := by
  unfold curvature
  abel

/-- Differential Bianchi identity follows from commuting coordinate derivatives. -/
theorem bianchi (A : ι → R) (D : ι → ι → R) (H : ι → ι → ι → R)
    (hH : ∀ k i j, H k i j = H i k j) (k i j : ι) :
    covariantExteriorPartial A D H k i j + covariantExteriorPartial A D H i j k +
      covariantExteriorPartial A D H j k i = 0 := by
  unfold covariantExteriorPartial curvaturePartial curvature
  have h₁ := hH k i j
  have h₂ := hH k j i
  have h₃ := hH i j k
  noncomm_ring [h₁, h₂, h₃]

end GaloisForLFunctions.HTGeometry.ConnectionBianchi
