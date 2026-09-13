import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring

/-!
# Two-bump exponential moment nondegeneracy

This module isolates the `2 × 2` determinant mechanism in formula (A.1) of the
Navier–Stokes paper.  Translating one bump by `Δ` multiplies its exponential moment
at exponent `s` by `exp (s * Δ)`.  Two distinct exponents therefore give an
invertible moment matrix whenever both original bump moments are nonzero.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesTwoBumpMoment

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
