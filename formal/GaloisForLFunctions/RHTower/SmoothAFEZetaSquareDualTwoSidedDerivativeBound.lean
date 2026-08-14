import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualSmallScaleDerivativeBound

noncomputable section

open Complex Set

namespace RHTower

/-- Exact two-sided localization of square-dual carrier derivative. Negative
quarter contour wins below square conductor; positive contour wins above it. -/
theorem exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_two_sided :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y) := by
  obtain ⟨A, hA, hsmall⟩ :=
    exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_small_scale
  obtain ⟨B, hB, hlarge⟩ :=
    exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_conductor_div_scale
  let C : ℝ := A + B
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro tau Y htau hY
  have htau0 : 0 < tau := by linarith
  have hden : 0 < tau * (tau ^ (1 / 4 : ℝ)) ^ 2 := by positivity
  have hsmall' := hsmall htau hY
  have hlarge' := hlarge htau hY
  apply le_min
  · refine hsmall'.trans ?_
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_right
      (show A ≤ C by dsimp only [C]; linarith) (by positivity)
  · refine hlarge'.trans ?_
    apply div_le_div_of_nonneg_right _ hY.le
    exact mul_le_mul_of_nonneg_right
      (show B ≤ C by dsimp only [C]; linarith) (by positivity)

end RHTower
