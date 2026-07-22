import GaloisForLFunctions.HTGeometry.ProjectiveHorizonComplementarity
import Mathlib.Tactic

/-!
# The reciprocal projective-horizon Ward seam

For a nonzero differential source `x`, the positive-jet frames of the reciprocal projective
charts `x` and `x⁻¹` differ by the reciprocal-square character `-x⁻²`.  Its logarithmic
connection is the doubled logarithmic current `-2 x′ / x`.

For the completed squarefree Euler amplitude this is the algebraic core identifying the general
HT reciprocal-horizon transition with the completed squarefree Ward current.  The analytic Hardy
projection is kept outside this file.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The transition between the two positive-jet horizon frames is the reciprocal-square
character. -/
theorem projectiveHorizon_reciprocalTransition
    {K : Type*} [Field K] [Differential K]
    (x : K) (hdx : x′ ≠ 0) :
    (x⁻¹)′ / x′ = -x⁻¹ ^ 2 := by
  rw [deriv_inv_eq_neg_inv_sq_mul_deriv]
  field_simp [hdx]

/-- The logarithmic connection on the reciprocal projective-horizon transition is the doubled
logarithmic current of the source. -/
theorem projectiveHorizon_reciprocalConnection
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x ≠ 0) (hdx : x′ ≠ 0) :
    (x⁻¹)′′ / (x⁻¹)′ - x′′ / x′ = -2 * (x′ / x) := by
  have hdinv : (x⁻¹)′ ≠ 0 := by
    rw [deriv_inv_eq_neg_inv_sq_mul_deriv]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero hx))) hdx
  rw [secondDeriv_inv_eq, deriv_inv_eq_neg_inv_sq_mul_deriv]
  field_simp [hx, hdx, hdinv]
  ring

/-- Hypertranscendence discharges nonvanishing of the source jet and makes the reciprocal
projective-horizon transition unconditional. -/
theorem hypertranscendentalOver_projectiveHorizon_reciprocalTransition
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (x : K) (hx : HypertranscendentalOver F x) :
    (x⁻¹)′ / x′ = -x⁻¹ ^ 2 := by
  apply projectiveHorizon_reciprocalTransition x
  simpa only [differentialJet_succ] using
    hypertranscendentalOver_differentialJet_ne_zero hx 1

/-- Hypertranscendence discharges both nonvanishing hypotheses in the reciprocal projective
connection law. -/
theorem hypertranscendentalOver_projectiveHorizon_reciprocalConnection
    {F K : Type*} [Field F] [Field K] [CharZero K] [Algebra F K] [Differential K]
    (x : K) (hx : HypertranscendentalOver F x) :
    (x⁻¹)′′ / (x⁻¹)′ - x′′ / x′ = -2 * (x′ / x) := by
  apply projectiveHorizon_reciprocalConnection x
  · simpa only [differentialJet_zero] using
      hypertranscendentalOver_differentialJet_ne_zero hx 0
  · simpa only [differentialJet_succ] using
      hypertranscendentalOver_differentialJet_ne_zero hx 1

end

end GaloisForLFunctions
