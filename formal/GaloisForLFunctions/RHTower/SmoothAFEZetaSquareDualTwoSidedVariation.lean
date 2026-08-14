import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualTwoSidedDerivativeBound

noncomputable section

open Complex Set

namespace RHTower

/-- Dyadic Lipschitz form of two-sided carrier localization. -/
theorem exists_norm_smoothAFEZetaSquareDualWeight_sub_le_dyadic_two_sided :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T Y tau u : ℝ}, 4 ≤ T → 0 < Y →
        tau ∈ Set.Icc T (2 * T) → u ∈ Set.Icc T (2 * T) →
        ‖smoothAFEZetaSquareDualWeight tau Y -
            smoothAFEZetaSquareDualWeight u Y‖ ≤
          min
            (C * Y ^ (1 / 4 : ℝ) /
              (T * (T ^ (1 / 4 : ℝ)) ^ 2))
            (C * (1 + 2 * T) / Y) * |tau - u| := by
  obtain ⟨C, hC, hderiv⟩ :=
    exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_two_sided
  refine ⟨C, hC, ?_⟩
  intro T Y tau u hT hY htau hu
  have hT0 : 0 < T := by linarith
  let f : ℝ → ℂ := fun y => smoothAFEZetaSquareDualWeight y Y
  let Lsmall : ℝ := C * Y ^ (1 / 4 : ℝ) /
    (T * (T ^ (1 / 4 : ℝ)) ^ 2)
  let Llarge : ℝ := C * (1 + 2 * T) / Y
  let L : ℝ := min Lsmall Llarge
  have hdiff : ∀ y ∈ Set.Icc T (2 * T), DifferentiableAt ℝ f y := by
    intro y hy
    exact (hasDerivAt_smoothAFEZetaSquareDualWeight hY y).differentiableAt
  have hbound : ∀ y ∈ Set.Icc T (2 * T), ‖deriv f y‖ ≤ L := by
    intro y hy
    have hy4 : 4 ≤ y := hT.trans hy.1
    have hy0 : 0 < y := by linarith
    have hraw := hderiv hy4 hY
    have hquarter : T ^ (1 / 4 : ℝ) ≤ y ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hT0.le hy.1 (by norm_num)
    have hqpow : (T ^ (1 / 4 : ℝ)) ^ 2 ≤
        (y ^ (1 / 4 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hquarter 2
    have hden : T * (T ^ (1 / 4 : ℝ)) ^ 2 ≤
        y * (y ^ (1 / 4 : ℝ)) ^ 2 := by
      exact mul_le_mul hy.1 hqpow (by positivity) hy0.le
    have hsmall :
        C * Y ^ (1 / 4 : ℝ) /
            (y * (y ^ (1 / 4 : ℝ)) ^ 2) ≤ Lsmall := by
      dsimp only [Lsmall]
      exact div_le_div_of_nonneg_left (by positivity)
        (by positivity) hden
    have hlarge : C * (1 + y) / Y ≤ Llarge := by
      dsimp only [Llarge]
      apply div_le_div_of_nonneg_right _ hY.le
      exact mul_le_mul_of_nonneg_left (by linarith [hy.2]) hC
    dsimp only [f, L]
    exact hraw.trans (min_le_min hsmall hlarge)
  have hmvt := (convex_Icc T (2 * T)).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound hu htau
  dsimp only [f, L, Lsmall, Llarge] at hmvt ⊢
  simpa [Real.norm_eq_abs] using hmvt

end RHTower
