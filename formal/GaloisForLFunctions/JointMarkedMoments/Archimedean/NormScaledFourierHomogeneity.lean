import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Norm-scaled archimedean Fourier homogeneity

On an `n`-dimensional real inner product space `V` (the archimedean completion `F ⊗ ℝ` with its
trace form), dilating a function by `Y^{−1/n}` multiplies its Fourier transform by the norm
volume `Y`: `𝓕(f(Y^{−1/n} ·))(ξ) = Y 𝓕f(Y^{1/n} ξ)` (Lemma 8.3). The real Jacobian of
`v ↦ Y^{1/n} v` is `(Y^{1/n})^n = Y`, so the leading norm-volume exponent does not grow with the
degree.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open MeasureTheory Real

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Dilation by `c⁻¹` multiplies the Fourier transform by `cⁿ` and dilates it by `c`. -/
theorem fourier_comp_inv_smul (f : V → E) {c : ℝ} (hc : 0 < c) (ξ : V) :
    𝓕 (fun v => f (c⁻¹ • v)) ξ = c ^ Module.finrank ℝ V • 𝓕 f (c • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V)
    (fun w : V => 𝐞 (-⟪c • w, ξ⟫_ℝ) • f w) hc.le
  have hcc : ∀ v : V, c • c⁻¹ • v = v := fun v => by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  simp only [hcc] at h
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [real_inner_smul_left, real_inner_smul_right]

/-- Lemma 8.3: `𝓕(f(Y^{−1/n} ·))(ξ) = Y 𝓕f(Y^{1/n} ξ)`, `n = dim V`. -/
theorem fourier_normScaled (f : V → E) {Y : ℝ} (hY : 0 < Y) (hn : Module.finrank ℝ V ≠ 0)
    (ξ : V) :
    𝓕 (fun v => f ((Y ^ (Module.finrank ℝ V : ℝ)⁻¹)⁻¹ • v)) ξ =
      Y • 𝓕 f (Y ^ (Module.finrank ℝ V : ℝ)⁻¹ • ξ) := by
  rw [fourier_comp_inv_smul f (Real.rpow_pos_of_pos hY _) ξ,
    Real.rpow_inv_natCast_pow hY.le hn]

end

end GaloisForLFunctions.JointMarkedMoments
