import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Source-pointed polarization order law

Exact coefficient preservation and Hermitian calibration do not commute.  Once a family of source
tests is total, its full coefficient packet has a unique reporter in the given Hilbert carrier.
Consequently no different same-carrier vector, and no nontrivial coefficient-preserving
endomorphism, can reduce its norm.  Any strictly smaller energy budget must first change the
carrier or the incidence pairing by an exact descent which removes a compatibility-redundant
direction.  Calibration can only occur after that descent.

This is the abstract rigidity behind the full-Euler reporter theorem: the division-free packet is
total and fixes an eight-unit reporter, while the physical boundary budget is four.  The mismatch
cannot be repaired by a different representative in the same carrier.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H I : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A family of source tests is total when its common left-orthogonal radical is zero. -/
def IsTotalTestFamily (test : I → H) : Prop :=
  ∀ x : H, (∀ i : I, inner ℂ x (test i) = 0) → x = 0

/-- **Coefficient rigidity.**  A total source-test family determines its reporter uniquely. -/
theorem IsTotalTestFamily.eq_of_coefficients
    {test : I → H} (htotal : IsTotalTestFamily test)
    {x y : H} (hcoeff : ∀ i : I, inner ℂ y (test i) = inner ℂ x (test i)) :
    y = x := by
  apply sub_eq_zero.mp
  apply htotal (y - x)
  intro i
  rw [inner_sub_left, hcoeff i, sub_self]

/-- **Descent-before-polarization obstruction.**  If the reporter already exceeds a prescribed
energy budget, no vector in the same Hilbert carrier can preserve every coefficient of a total
test family and meet that budget. -/
theorem IsTotalTestFamily.no_strict_budget_reporter
    {test : I → H} (htotal : IsTotalTestFamily test)
    {x : H} {B : ℝ} (hbudget : B < ‖x‖ ^ (2 : ℕ)) :
    ¬ ∃ y : H,
      (∀ i : I, inner ℂ y (test i) = inner ℂ x (test i)) ∧
      ‖y‖ ^ (2 : ℕ) ≤ B := by
  rintro ⟨y, hcoeff, hy⟩
  rw [htotal.eq_of_coefficients hcoeff] at hy
  exact (not_le_of_gt hbudget) hy

/-- A coefficient-preserving endomorphism of a carrier with a total test family is the identity.
Thus same-carrier preprocessing cannot perform a nontrivial Hermitian compression while retaining
the complete packet. -/
theorem IsTotalTestFamily.coefficient_preserving_endomorphism_eq_id
    {test : I → H} (htotal : IsTotalTestFamily test)
    (C : H →ₗ[ℂ] H)
    (hcoeff : ∀ x : H, ∀ i : I,
      inner ℂ (C x) (test i) = inner ℂ x (test i)) :
    C = LinearMap.id := by
  ext x
  exact htotal.eq_of_coefficients (hcoeff x)

end

end GaloisForLFunctions.HTGeometry
