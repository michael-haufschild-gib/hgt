import GaloisForLFunctions.RHTower.SuzukiGammaStripSquareIntegrable
import GaloisForLFunctions.HTGeometry.GammaVerticalSubstripBound

/-!
# The glued strip solution is bounded on every closed substrip

On `σ₀ ≤ Im z ≤ σ₁` with `0 < σ₀ ≤ σ₁ < 1` the three factors of the strip solution are separately
bounded: `|z|^{-1/2}` because `|z| ≥ Im z ≥ σ₀`, the operator exponential because `T` is
self-adjoint and the strip has bounded width, and the Gamma quotient by the Beta bound together
with the compactness of the height interval.  A uniform sup bound on a closed substrip is what a
contour shift needs in order to discard the two vertical segments.
-/

open Set Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

/-- The strip carrier density is bounded on a closed substrip. -/
theorem suzukiGammaStripNormSq_le_of_mem {σ₀ σ₁ : ℝ} (h0 : 0 < σ₀) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y ∈ Icc σ₀ σ₁, ∀ x : ℝ,
      ‖Complex.Gamma (((1 - y : ℝ) : ℂ) + (x : ℂ) * I)‖
        / ‖Complex.Gamma (((1 + y : ℝ) : ℂ) + (x : ℂ) * I)‖ ≤ K)
    {σ : ℝ} (hσ : σ ∈ Icc σ₀ σ₁) (x : ℝ) :
    suzukiGammaStripNormSq σ x ≤ K / σ₀ := by
  have hnorm : σ₀ ≤ ‖(x : ℂ) + (σ : ℂ) * I‖ := by
    refine le_trans hσ.1 (le_trans (le_abs_self σ) ?_)
    have him : ((x : ℂ) + (σ : ℂ) * I).im = σ := by simp
    have := Complex.abs_im_le_norm ((x : ℂ) + (σ : ℂ) * I)
    rwa [him] at this
  rw [suzukiGammaStripNormSq]
  exact div_le_div₀ hK0 (hK σ hσ x) h0 hnorm

/-- **The glued strip solution is uniformly bounded on every closed substrip.** -/
theorem exists_bound_norm_stripSolution {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) (c : X) {σ₀ σ₁ : ℝ} (h0 : 0 < σ₀)
    (h01 : σ₀ ≤ σ₁) (h1 : σ₁ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℂ, z.im ∈ Icc σ₀ σ₁ → ‖stripSolution E T c z‖ ≤ D := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_gammaRatio_substrip h0 h01 h1
  set B : ℝ := (Real.exp (2 * |Real.eulerMascheroniConstant|) * Real.exp ‖T‖ * ‖c‖ ^ 2) * (K / σ₀)
    with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ K / σ₀ := div_nonneg hK0 h0.le
    positivity
  refine ⟨Real.sqrt B, Real.sqrt_nonneg B, fun z hz => ?_⟩
  set σ : ℝ := z.im with hσdef
  have hσ0 : 0 < σ := lt_of_lt_of_le h0 hz.1
  have hσ1 : σ < 1 := lt_of_le_of_lt hz.2 h1
  have hzeq : ((z.re : ℂ)) + (σ : ℂ) * I = z := by
    rw [hσdef]; exact Complex.re_add_im z
  have hsq := norm_sq_stripSolution_shift_le hT hE c hσ0 hσ1 z.re
  rw [hzeq] at hsq
  have hfac1 : Real.exp (-(2 * Real.eulerMascheroniConstant * σ))
      ≤ Real.exp (2 * |Real.eulerMascheroniConstant|) := by
    refine Real.exp_le_exp.mpr ?_
    have habs : |2 * Real.eulerMascheroniConstant * σ|
        ≤ 2 * |Real.eulerMascheroniConstant| := by
      rw [abs_mul, abs_mul]
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      have hσabs : |σ| ≤ 1 := by
        rw [abs_of_pos hσ0]
        linarith
      calc 2 * |Real.eulerMascheroniConstant| * |σ|
          ≤ 2 * |Real.eulerMascheroniConstant| * 1 :=
            mul_le_mul_of_nonneg_left hσabs (by positivity)
        _ = 2 * |Real.eulerMascheroniConstant| := by ring
    linarith [neg_le_abs (2 * Real.eulerMascheroniConstant * σ)]
  have hfac2 : Real.exp (σ * ‖T‖) ≤ Real.exp ‖T‖ := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [norm_nonneg T]
  have hcarrier : suzukiGammaStripNormSq σ z.re ≤ K / σ₀ :=
    suzukiGammaStripNormSq_le_of_mem h0 hK0 hK ⟨hz.1, hz.2⟩ z.re
  have hcarrier0 : 0 ≤ suzukiGammaStripNormSq σ z.re := by
    rw [suzukiGammaStripNormSq]
    positivity
  have hchain : ‖stripSolution E T c z‖ ^ 2 ≤ B := by
    refine le_trans hsq ?_
    rw [hB]
    refine mul_le_mul ?_ hcarrier hcarrier0 (by positivity)
    refine mul_le_mul (mul_le_mul hfac1 hfac2 (by positivity) (by positivity)) (le_refl _)
      (by positivity) (by positivity)
  have := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

end

end GaloisForLFunctions.RHTower
