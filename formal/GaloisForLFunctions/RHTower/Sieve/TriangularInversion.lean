import GaloisForLFunctions.RHTower.Sieve.TriangularKernel

/-!
# Fourier inversion for the triangular kernel

The triangular kernel is continuous and compactly supported, and its Fourier transform is the Fejér
weight, which the corpus bounds by both the interval length and `L^{-2}`.  Those two bounds together
dominate the transform by a Lorentzian, so it is integrable and Fourier inversion applies:

    𝓕⁻ (𝓕 (δ - |·|)₊) = (δ - |·|)₊ .

This is the second half of Gallagher's reduction: it expresses the overlap kernel of two windows as
an integral of a nonnegative, explicitly decaying weight against a phase.
-/

namespace RHTower.Sieve

open Complex MeasureTheory FourierTransform Real

/-- The triangular kernel as a complex-valued function. -/
noncomputable def triC (δ : ℝ) : ℝ → ℂ := fun t => ((tri δ t : ℝ) : ℂ)

theorem continuous_triC (δ : ℝ) : Continuous (triC δ) :=
  Complex.continuous_ofReal.comp (continuous_tri δ)

theorem hasCompactSupport_triC {δ : ℝ} (hδ : 0 ≤ δ) : HasCompactSupport (triC δ) := by
  refine HasCompactSupport.intro (K := Set.Icc (-δ) δ) isCompact_Icc fun x hx => ?_
  have habs : δ ≤ |x| := by
    rw [Set.mem_Icc] at hx
    push Not at hx
    rcases le_or_gt (-δ) x with h | h
    · have := hx h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonpos (by linarith)]
      linarith
  rw [triC]
  simp [tri_eq_zero habs]

theorem integrable_triC {δ : ℝ} (hδ : 0 ≤ δ) : Integrable (triC δ) :=
  (continuous_triC δ).integrable_of_hasCompactSupport (hasCompactSupport_triC hδ)

/-- **The Fourier transform of the triangular kernel is the Fejér weight.** -/
theorem fourier_triC {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    𝓕 (triC δ) w = (δ : ℂ) * fejerWeightAt δ (-(2 * Real.pi * w)) := by
  rw [Real.fourier_real_eq, ← integral_tri_phase hδ (-(2 * Real.pi * w))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [triC, Circle.smul_def, Real.fourierChar_apply]
  rw [show ((2 * Real.pi * -(v * w) : ℝ) : ℂ) = ((v * -(2 * Real.pi * w) : ℝ) : ℂ) by
    push_cast; ring]
  ring

theorem continuous_fourier_triC {δ : ℝ} (hδ : 0 ≤ δ) : Continuous (𝓕 (triC δ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (L := (innerSL ℝ (E := ℝ)).toLinearMap₁₂) (by fun_prop) (integrable_triC hδ)

/-- The transform is dominated by a Lorentzian: the interval-length bound and the `L^{-2}` bound
combine into an integrable majorant. -/
theorem norm_fourier_triC_le {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    ‖𝓕 (triC δ) w‖ ≤ 2 * δ ^ (2 : ℕ) / (1 + (δ * Real.pi * w) ^ (2 : ℕ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hden : (0 : ℝ) < 1 + (δ * Real.pi * w) ^ (2 : ℕ) := by positivity
  rw [fourier_triC hδ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
    le_div_iff₀ hden]
  rcases eq_or_ne w 0 with rfl | hw
  · rw [show -(2 * Real.pi * (0 : ℝ)) = 0 by ring, fejerWeightAt_zero hδ,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    have : δ * Real.pi * (0 : ℝ) = 0 := by ring
    rw [this]
    nlinarith
  · set L : ℝ := -(2 * Real.pi * w) with hLdef
    have hL0 : L ≠ 0 := by
      rw [hLdef]
      intro h
      have : Real.pi * w = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (ne_of_gt hpi)
      · exact hw h'
    have hLsq : L ^ (2 : ℕ) = 4 * Real.pi ^ (2 : ℕ) * w ^ (2 : ℕ) := by rw [hLdef]; ring
    have hLsqpos : (0 : ℝ) < L ^ (2 : ℕ) := by positivity
    have h1 : ‖fejerWeightAt δ L‖ ≤ 4 / (δ * L ^ (2 : ℕ)) := norm_fejerWeightAt_le hδ hL0
    have h2 : ‖fejerWeightAt δ L‖ ≤ δ := by
      rw [fejerWeightAt]
      exact norm_integral_fejer_symm_le_len L hL0 hδ
    have hx0 : (0 : ℝ) ≤ ‖fejerWeightAt δ L‖ := norm_nonneg _
    have hkey : ‖fejerWeightAt δ L‖ * (δ * Real.pi ^ (2 : ℕ) * w ^ (2 : ℕ)) ≤ 1 := by
      have hstep : ‖fejerWeightAt δ L‖ * (δ * L ^ (2 : ℕ)) ≤ 4 := by
        rw [← le_div_iff₀ (by positivity)]
        exact h1
      rw [hLsq] at hstep
      nlinarith
    nlinarith [hkey, h2, hx0, sq_nonneg w, hδ.le]

theorem integrable_fourier_triC {δ : ℝ} (hδ : 0 < δ) : Integrable (𝓕 (triC δ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hne : δ * Real.pi ≠ 0 := by positivity
  have hlor : Integrable fun w : ℝ => (1 + (δ * Real.pi * w) ^ (2 : ℕ))⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' hne
  have hmaj : Integrable fun w : ℝ => 2 * δ ^ (2 : ℕ) * (1 + (δ * Real.pi * w) ^ (2 : ℕ))⁻¹ :=
    hlor.const_mul _
  refine Integrable.mono' hmaj (continuous_fourier_triC hδ.le).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun w => ?_
  have := norm_fourier_triC_le hδ w
  rwa [div_eq_mul_inv] at this

/-- **Fourier inversion for the triangular kernel.** -/
theorem fourierInv_fourier_triC {δ : ℝ} (hδ : 0 < δ) :
    𝓕⁻ (𝓕 (triC δ)) = triC δ :=
  (continuous_triC δ).fourierInv_fourier_eq (integrable_triC hδ.le) (integrable_fourier_triC hδ)

end RHTower.Sieve
