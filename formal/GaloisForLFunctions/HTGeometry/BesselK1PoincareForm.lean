import GaloisForLFunctions.HTGeometry.BesselK1AllOrderAsymptotic

/-!
# The Poincaré form of the order-one Schläfli asymptotic

Every even Gaussian moment is a rational multiple of `w^{-k}` times the Gaussian integral, so the
Watson expansion of `K_1` collapses to the classical Poincaré form: `e^{-w}(π/w)^{1/2}` times a
polynomial in `1/w`, plus the same fixed-order remainder.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Poincare

variable {w : ℂ}

/-- The double-factorial normalisation of the even Gaussian moments. -/
def gaussianMomentFactor (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, ((2 * (j : ℝ) + 1) / 2)

/-- The Poincaré coefficients of the order-one Schläfli asymptotic. -/
def besselK1Coeff (k : ℕ) : ℝ := schlafliCoeff k * gaussianMomentFactor k

theorem prod_two_mul_add_one_div (w : ℂ) (hwne : w ≠ 0) (k : ℕ) :
    (∏ j ∈ Finset.range k, ((2 * (j : ℂ) + 1) / (2 * w)))
      = (∏ j ∈ Finset.range k, ((2 * (j : ℂ) + 1) / 2)) * (w⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
      field_simp

theorem gaussianHalfMoment_eq_pow (hw : 0 < w.re) (k : ℕ) :
    gaussianHalfMoment w k
      = ((gaussianMomentFactor k : ℝ) : ℂ) * (w⁻¹) ^ k
        * (((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ) / 2) := by
  have hwne : w ≠ 0 := _root_.HTGeometry.ne_zero_of_re_pos hw
  have hprod : (∏ j ∈ Finset.range k, ((2 * (j : ℂ) + 1) / (2 * w)))
      = ((gaussianMomentFactor k : ℝ) : ℂ) * (w⁻¹) ^ k := by
    have hcast : ((gaussianMomentFactor k : ℝ) : ℂ)
        = ∏ j ∈ Finset.range k, ((2 * (j : ℂ) + 1) / 2) := by
      rw [gaussianMomentFactor]
      push_cast
      rfl
    rw [hcast]
    exact prod_two_mul_add_one_div w hwne k
  rw [gaussianHalfMoment_eq hw k, hprod]

/-- **The Poincaré form.**  The Watson expansion of `K_1` is `e^{-w}(π/w)^{1/2}` times a polynomial
in `1/w`, with the same fixed-order remainder. -/
theorem norm_besselK1C_sub_poincare_le (hw : 0 < w.re) (m : ℕ) :
    ‖_root_.HTGeometry.besselK1C w
        - Complex.exp (-w) * ((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ)
          * ∑ k ∈ Finset.range (m + 1), ((besselK1Coeff k : ℝ) : ℂ) * (w⁻¹) ^ k‖
      ≤ 2 * Real.exp (-w.re) * ((3 * (Real.sqrt 2)⁻¹ / 2 ^ (m + 1))
        * realGaussianHalfMoment w.re (m + 1)) := by
  have hrw : 2 * Complex.exp (-w)
      * ∑ k ∈ Finset.range (m + 1), ((schlafliCoeff k : ℝ) : ℂ) * gaussianHalfMoment w k
      = Complex.exp (-w) * ((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ)
        * ∑ k ∈ Finset.range (m + 1), ((besselK1Coeff k : ℝ) : ℂ) * (w⁻¹) ^ k := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [gaussianHalfMoment_eq_pow hw k, besselK1Coeff]
    push_cast
    ring
  rw [← hrw]
  exact norm_besselK1C_sub_watson_le hw m

end Poincare

end

end GaloisForLFunctions.HTGeometry
