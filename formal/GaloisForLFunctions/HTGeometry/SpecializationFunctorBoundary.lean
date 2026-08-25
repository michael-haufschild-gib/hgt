import GaloisForLFunctions.HTGeometry.MultiplierDichotomyDegreeObstruction
import GaloisForLFunctions.HTGeometry.SpecializationFaithfulnessBoundary
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic

/-!
# Exact coefficient-ring boundary for the proposed C6 specialization functors

The rank-one Euler multiplier is a rational `q`-coboundary, so it gives a valid difference module
after passing to a rational-function coefficient field.  It is not, however, a unit of the Laurent
polynomial ring used as the domain of the proposed C6 category.  Evaluation at `x = 1` makes the
obstruction immediate: every Laurent unit remains nonzero, whereas the numerator `1 - x` vanishes
and the denominator `1 - x / 2` does not.

This file also imports the separate point-specialization faithfulness boundary: a point evaluation
is not faithful on unrestricted polynomial scalar morphisms, while the full evaluation profile is.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open LaurentPolynomial Polynomial

/-- Evaluation of a Laurent polynomial at the unit coordinate `1`. -/
def laurentEvalOne : LaurentPolynomial ℂ →+* ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) (1 : ℂˣ)

@[simp]
theorem laurentEvalOne_T_one :
    laurentEvalOne (LaurentPolynomial.T 1 : LaurentPolynomial ℂ) = 1 := by
  simp [laurentEvalOne]

/-- The local Euler denominator is not invertible in the Laurent polynomial coefficient ring. -/
theorem one_sub_laurentCoordinate_not_isUnit :
    ¬ IsUnit (1 - LaurentPolynomial.T 1 : LaurentPolynomial ℂ) := by
  intro hunit
  have himage : IsUnit
      (laurentEvalOne (1 - LaurentPolynomial.T 1 : LaurentPolynomial ℂ)) :=
    hunit.map laurentEvalOne
  simpa using himage.ne_zero

/-- At `q = 1/2`, no Laurent unit can represent the Euler difference multiplier
`(1 - x) / (1 - qx)`. -/
theorem twoEulerDifferenceMultiplier_not_laurentUnit :
    ¬ ∃ a : LaurentPolynomial ℂ, IsUnit a ∧
      (1 - LaurentPolynomial.C ((2 : ℂ)⁻¹) * LaurentPolynomial.T 1) * a =
        1 - LaurentPolynomial.T 1 := by
  rintro ⟨a, ha, heq⟩
  have haeval : laurentEvalOne a ≠ 0 := (ha.map laurentEvalOne).ne_zero
  have h := congrArg laurentEvalOne heq
  simp [laurentEvalOne] at h
  rcases h with hden | ha0
  · norm_num at hden
  · exact haeval ha0

/-- Sharp C6 survivor: the Euler multiplier is a rational `q`-coboundary, but it cannot be the
`GL₁` coefficient claimed over the unlocalized Laurent ring. -/
theorem c6_rankOneEuler_laurentBoundary :
    GaloisForLFunctions.OrbitBalanceComplete.IsCCq
        ((2 : ℂ)⁻¹) (by norm_num)
        (algebraMap ℂ[X] (RatFunc ℂ) (1 - X) /
          algebraMap ℂ[X] (RatFunc ℂ)
            (1 - Polynomial.C ((2 : ℂ)⁻¹) * X)) ∧
      ¬ IsUnit (1 - LaurentPolynomial.T 1 : LaurentPolynomial ℂ) ∧
      ¬ ∃ a : LaurentPolynomial ℂ, IsUnit a ∧
        (1 - LaurentPolynomial.C ((2 : ℂ)⁻¹) * LaurentPolynomial.T 1) * a =
          1 - LaurentPolynomial.T 1 := by
  exact ⟨GaloisForLFunctions.MultiplierDichotomyComplete.isCCq_eulerMultiplier
      (by norm_num),
    one_sub_laurentCoordinate_not_isUnit,
    twoEulerDifferenceMultiplier_not_laurentUnit⟩

end


end GaloisForLFunctions.HTGeometry
