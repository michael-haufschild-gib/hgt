import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Ring

/-!
# Two-bump exponential moment nondegeneracy

This module isolates the `2 × 2` determinant mechanism in formula (A.1) of the
Navier–Stokes paper.  Translating one bump by `Δ` multiplies its exponential moment
at exponent `s` by `exp (s * Δ)`.  Two distinct exponents therefore give an
invertible moment matrix whenever both original bump moments are nonzero.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesTwoBumpMoment

open MeasureTheory

/-- Exponential moment of a bump in logarithmic coordinates. -/
noncomputable def exponentialBumpMoment (β : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x, Real.exp (s * x) * β x ∂volume

/-- Exponential moment after translating the bump center by `c`. -/
noncomputable def translatedExponentialBumpMoment (β : ℝ → ℝ) (c s : ℝ) : ℝ :=
  ∫ x, Real.exp (s * x) * β (x - c) ∂volume

/-- Translating a bump by `c` multiplies its exponential moment by `exp (s*c)`. -/
theorem translatedExponentialBumpMoment_eq
    (β : ℝ → ℝ) (c s : ℝ) :
    translatedExponentialBumpMoment β c s =
      Real.exp (s * c) * exponentialBumpMoment β s := by
  calc
    translatedExponentialBumpMoment β c s =
        ∫ x : ℝ, Real.exp (s * (x + c)) * β (x + c - c) ∂volume := by
          unfold translatedExponentialBumpMoment
          exact (MeasureTheory.integral_add_right_eq_self
            (μ := (volume : Measure ℝ))
            (fun x : ℝ => Real.exp (s * x) * β (x - c)) c).symm
    _ =
        ∫ x : ℝ, Real.exp (s * c) * (Real.exp (s * x) * β x) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [add_sub_cancel_right, mul_add, Real.exp_add]
          ring
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]
      rfl

/-- Actual two-translated-bump moment matrix before row normalization in formula (A.1). -/
noncomputable def translatedTwoBumpMomentMatrix
    (β : ℝ → ℝ) (c s₁ s₂ Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![translatedExponentialBumpMoment β c s₁,
      translatedExponentialBumpMoment β (c + Δ) s₁;
     translatedExponentialBumpMoment β c s₂,
      translatedExponentialBumpMoment β (c + Δ) s₂]

/-- Determinant factorization for the actual translated-bump moment integrals. -/
theorem det_translatedTwoBumpMomentMatrix
    (β : ℝ → ℝ) (c s₁ s₂ Δ : ℝ) :
    (translatedTwoBumpMomentMatrix β c s₁ s₂ Δ).det =
      Real.exp ((s₁ + s₂) * c) *
        exponentialBumpMoment β s₁ * exponentialBumpMoment β s₂ *
          (Real.exp (s₂ * Δ) - Real.exp (s₁ * Δ)) := by
  simp [translatedTwoBumpMomentMatrix, Matrix.det_fin_two,
    translatedExponentialBumpMoment_eq]
  rw [mul_add s₁ c Δ, mul_add s₂ c Δ, Real.exp_add, Real.exp_add]
  rw [add_mul, Real.exp_add]
  ring

/-- Normalized two-bump moment matrix from formula (A.1). -/
noncomputable def twoBumpMomentMatrix (b : ℝ → ℝ) (s₁ s₂ Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b s₁, Real.exp (s₁ * Δ) * b s₁;
     b s₂, Real.exp (s₂ * Δ) * b s₂]

/-- The exact determinant factorization behind the two-bump case of Lemma A.1. -/
theorem det_twoBumpMomentMatrix (b : ℝ → ℝ) (s₁ s₂ Δ : ℝ) :
    (twoBumpMomentMatrix b s₁ s₂ Δ).det =
      b s₁ * b s₂ * (Real.exp (s₂ * Δ) - Real.exp (s₁ * Δ)) := by
  simp [twoBumpMomentMatrix, Matrix.det_fin_two]
  ring

/-- Ordered exponents and positive separation give a strictly positive exponential gap. -/
theorem exp_gap_pos {s₁ s₂ Δ : ℝ} (hs : s₁ < s₂) (hΔ : 0 < Δ) :
    0 < Real.exp (s₂ * Δ) - Real.exp (s₁ * Δ) := by
  rw [sub_pos, Real.exp_lt_exp]
  exact mul_lt_mul_of_pos_right hs hΔ

/-- Positive base moments make the determinant of the actual translated-bump matrix positive. -/
theorem det_translatedTwoBumpMomentMatrix_pos (β : ℝ → ℝ) (c : ℝ) {s₁ s₂ Δ : ℝ}
    (hb₁ : 0 < exponentialBumpMoment β s₁)
    (hb₂ : 0 < exponentialBumpMoment β s₂) (hs : s₁ < s₂) (hΔ : 0 < Δ) :
    0 < (translatedTwoBumpMomentMatrix β c s₁ s₂ Δ).det := by
  rw [det_translatedTwoBumpMomentMatrix]
  exact mul_pos (mul_pos (mul_pos (Real.exp_pos _) hb₁) hb₂) (exp_gap_pos hs hΔ)

/-- Two translated bumps independently control two actual exponential-moment integrals. -/
theorem isUnit_translatedTwoBumpMomentMatrix (β : ℝ → ℝ) (c : ℝ) {s₁ s₂ Δ : ℝ}
    (hb₁ : 0 < exponentialBumpMoment β s₁)
    (hb₂ : 0 < exponentialBumpMoment β s₂) (hs : s₁ < s₂) (hΔ : 0 < Δ) :
    IsUnit (translatedTwoBumpMomentMatrix β c s₁ s₂ Δ) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact (det_translatedTwoBumpMomentMatrix_pos β c hb₁ hb₂ hs hΔ).ne'

/-- Positive bump moments make the normalized determinant positive. -/
theorem det_twoBumpMomentMatrix_pos (b : ℝ → ℝ) {s₁ s₂ Δ : ℝ}
    (hb₁ : 0 < b s₁) (hb₂ : 0 < b s₂) (hs : s₁ < s₂) (hΔ : 0 < Δ) :
    0 < (twoBumpMomentMatrix b s₁ s₂ Δ).det := by
  rw [det_twoBumpMomentMatrix]
  exact mul_pos (mul_pos hb₁ hb₂) (exp_gap_pos hs hΔ)

/-- Nonzero bump moments suffice for nondegeneracy; their signs need not agree. -/
theorem det_twoBumpMomentMatrix_ne_zero (b : ℝ → ℝ) {s₁ s₂ Δ : ℝ}
    (hb₁ : b s₁ ≠ 0) (hb₂ : b s₂ ≠ 0) (hs : s₁ < s₂) (hΔ : 0 < Δ) :
    (twoBumpMomentMatrix b s₁ s₂ Δ).det ≠ 0 := by
  rw [det_twoBumpMomentMatrix]
  exact mul_ne_zero (mul_ne_zero hb₁ hb₂) (ne_of_gt (exp_gap_pos hs hΔ))

/-- The two translated bumps independently control the two exponential moments. -/
theorem isUnit_twoBumpMomentMatrix (b : ℝ → ℝ) {s₁ s₂ Δ : ℝ}
    (hb₁ : b s₁ ≠ 0) (hb₂ : b s₂ ≠ 0) (hs : s₁ < s₂) (hΔ : 0 < Δ) :
    IsUnit (twoBumpMomentMatrix b s₁ s₂ Δ) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact det_twoBumpMomentMatrix_ne_zero b hb₁ hb₂ hs hΔ

end GaloisForLFunctions.HTGeometry.NavierStokesTwoBumpMoment
