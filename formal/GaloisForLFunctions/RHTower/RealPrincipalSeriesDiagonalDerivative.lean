import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactHarishChandra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Positive-diagonal derivative in the real compact principal series

This file constructs the positive diagonal one-parameter subgroup and differentiates its actual
compact-picture action at the identity of `K`.  Full Iwasawa-coordinate differentiation and its
identification with the raising and lowering operators are proved in
`RealPrincipalSeriesDiagonalKTypeDerivative`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Positive diagonal one-parameter subgroup, regarded as an element of the upper Borel. -/
def realPositiveDiagonalBorel (t : ℝ) : realUpperBorel :=
  ⟨⟨!![Real.exp t, 0; 0, Real.exp (-t)], by
      simp [Matrix.det_fin_two, Real.exp_neg]⟩, by simp⟩

@[simp]
theorem realPositiveDiagonalBorel_zero : realPositiveDiagonalBorel 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realPositiveDiagonalBorel]

theorem realPositiveDiagonalBorel_add (t u : ℝ) :
    realPositiveDiagonalBorel (t + u) =
      realPositiveDiagonalBorel t * realPositiveDiagonalBorel u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realPositiveDiagonalBorel, Matrix.mul_apply, Fin.sum_univ_two,
      Real.exp_add]
  all_goals ring

@[simp]
theorem realPositiveDiagonalBorel_character (σ t : ℝ) :
    realUpperBorelRpowCharacter σ (realPositiveDiagonalBorel t) =
      (Real.exp (t * σ) : ℂ) := by
  change ((|Real.exp t| ^ σ : ℝ) : ℂ) = _
  rw [abs_of_pos (Real.exp_pos t), ← Real.exp_mul]

@[simp]
theorem compactRealPrincipalSeries_positiveDiagonal_one_apply
    (σ t : ℝ) (φ : realCompactPictureSpace σ) :
    ((compactRealPrincipalSeries σ (realPositiveDiagonalBorel t : SL2R)) φ).1 1 =
      (Real.exp (t * σ) : ℂ) * φ.1 1 := by
  rw [compactRealPrincipalSeries_factor_apply σ
    (realPositiveDiagonalBorel t : SL2R) 1 φ (realPositiveDiagonalBorel t) 1]
  · rw [realPositiveDiagonalBorel_character]
  · simp

/-- At the identity of `K`, the positive-diagonal derivative is multiplication by the inducing
exponent. -/
theorem hasDerivAt_compactRealPrincipalSeries_positiveDiagonal_one
    (σ : ℝ) (φ : realCompactPictureSpace σ) :
    HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries σ (realPositiveDiagonalBorel t : SL2R)) φ).1 1)
      ((σ : ℂ) * φ.1 1) 0 := by
  have hr : HasDerivAt (fun t : ℝ => Real.exp (t * σ)) σ 0 := by
    convert! (Real.hasDerivAt_exp (0 * σ)).comp 0
      ((hasDerivAt_id 0).mul_const σ) using 1
    all_goals norm_num
  have hc : HasDerivAt (fun t : ℝ => (Real.exp (t * σ) : ℂ)) (σ : ℂ) 0 :=
    hr.ofReal_comp
  simpa only [compactRealPrincipalSeries_positiveDiagonal_one_apply] using
    hc.mul_const (φ.1 1)

end
end GaloisForLFunctions.RHTower
