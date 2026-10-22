import GaloisForLFunctions.RHTower.CCM.CCMCoherentMidpointFourier

/-!
# The signed current and energy retain the same arithmetic sine sum

Plancherel identifies the odd energy with the square of the full sine sum.
The signed current is the product of that sum with the increment sine.
These identities hold for every complex `L²` source, without a parity assumption.
-/

noncomputable section
open Complex MeasureTheory
open scoped InnerProduct BigOperators

namespace RHTower

/-- The translation increment has the same midpoint phase as the odd field. -/
theorem fourierPhase_sub_one_midpoint (r ξ : ℝ) :
    MellinL2.fourierPhase r ξ - 1 =
      2 * Complex.I * MellinL2.fourierPhase (r/2) ξ * (Real.sin (Real.pi*r*ξ) : ℂ) := by
  have h := fourierPhase_midpoint_half_sub r (-r) ξ
  have hzero : MellinL2.fourierPhase 0 ξ = 1 := by
    simp [MellinL2.fourierPhase]
  have ha : 2*Real.pi*(-r+r/2)*ξ = -(Real.pi*r*ξ) := by ring
  rw [neg_neg, add_neg_cancel, hzero, ha, Real.sin_neg, Complex.ofReal_neg] at h
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  linear_combination 2 * h

theorem fourier_logTranslation_increment_ae (r : ℝ) (f : SoninL2) :
    (fourierUnitary (logTranslationCLM r f - f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (2 * Complex.I * MellinL2.fourierPhase (r/2) ξ *
        (Real.sin (Real.pi*r*ξ) : ℂ)) * fourierUnitary f ξ := by
  have ht : fourierUnitary (logTranslationCLM r f) =
      MellinL2.fourierPhaseMulUnitary r (fourierUnitary f) :=
    MellinL2.fourier_additiveTranslation r f
  rw [map_sub, ht]
  filter_upwards [Lp.coeFn_sub
    (MellinL2.fourierPhaseMulUnitary r (fourierUnitary f)) (fourierUnitary f),
    MellinL2.fourierPhaseMulAux_ae r (fourierUnitary f)] with ξ hs ht
  rw [hs, Pi.sub_apply]
  change MellinL2.fourierPhaseMulAux r (fourierUnitary f) ξ - fourierUnitary f ξ = _
  rw [ht]
  calc
    _ = (MellinL2.fourierPhase r ξ - 1) * fourierUnitary f ξ := by ring
    _ = _ := by rw [fourierPhase_sub_one_midpoint]

private theorem odd_norm_sq (r ξ b : ℝ) (z : ℂ) :
    ‖(-Complex.I * MellinL2.fourierPhase (r/2) ξ * (b : ℂ)) * z‖ ^ 2 =
      b^2 * ‖z‖^2 := by
  simp only [norm_mul, norm_neg, Complex.norm_I, MellinL2.norm_fourierPhase,
    Complex.norm_real, Real.norm_eq_abs, one_mul, mul_pow, sq_abs]

/-- The energy contains the square of the signed sum, with every cross term intact. -/
theorem norm_sq_ccmActualHeadMidpointOddField_eq_spectral (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadMidpointOddField T N f r‖ ^ 2 =
      ∫ ξ : ℝ, (ccmActualHeadMidpointSineSymbol T N r ξ)^2 * ‖fourierUnitary f ξ‖^2 := by
  rw [← fourierUnitary.norm_map (ccmActualHeadMidpointOddField T N f r), norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [fourier_ccmActualHeadMidpointOddField_ae T N f r] with ξ hξ
  rw [hξ, odd_norm_sq]

theorem integrable_ccmActualHeadMidpointSineEnergy (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    Integrable (fun ξ : ℝ =>
      (ccmActualHeadMidpointSineSymbol T N r ξ)^2 * ‖fourierUnitary f ξ‖^2) := by
  refine ((Lp.memLp (fourierUnitary (ccmActualHeadMidpointOddField T N f r))).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)).congr ?_
  filter_upwards [fourier_ccmActualHeadMidpointOddField_ae T N f r] with ξ hξ
  rw [hξ, odd_norm_sq]

/-- The real multiplier of the full signed current. -/
def ccmActualHeadMidpointCurrentSymbol (T : ℝ) (N : ℕ) (r ξ : ℝ) : ℝ :=
  -2 * Real.sin (Real.pi*r*ξ) * ccmActualHeadMidpointSineSymbol T N r ξ

private theorem sine_pair_inner (a b : ℝ) (z : ℂ) :
    (inner ℂ ((2*Complex.I*(a : ℂ)) * z) ((-Complex.I*(b : ℂ)) * z)).re =
      -2*a*b*‖z‖^2 := by
  change (inner ℂ ((2*Complex.I*(a : ℂ)) • z) ((-Complex.I*(b : ℂ)) • z)).re = _
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]; ring

private theorem current_integrand_ae (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    (fun ξ : ℝ => (inner ℂ (fourierUnitary (logTranslationCLM r f - f) ξ)
      (fourierUnitary (ccmActualHeadMidpointOddField T N f r) ξ)).re) =ᵐ[volume]
    fun ξ => ccmActualHeadMidpointCurrentSymbol T N r ξ * ‖fourierUnitary f ξ‖^2 := by
  filter_upwards [fourier_logTranslation_increment_ae r f,
    fourier_ccmActualHeadMidpointOddField_ae T N f r] with ξ hδ hO
  rw [hδ, hO]
  have h₁ : (2*Complex.I*MellinL2.fourierPhase (r/2) ξ*(Real.sin (Real.pi*r*ξ) : ℂ)) *
      fourierUnitary f ξ = (2*Complex.I*(Real.sin (Real.pi*r*ξ) : ℂ)) *
        (MellinL2.fourierPhase (r/2) ξ * fourierUnitary f ξ) := by ring
  have h₂ : (-Complex.I*MellinL2.fourierPhase (r/2) ξ*
      (ccmActualHeadMidpointSineSymbol T N r ξ : ℂ)) * fourierUnitary f ξ =
      (-Complex.I*(ccmActualHeadMidpointSineSymbol T N r ξ : ℂ)) *
        (MellinL2.fourierPhase (r/2) ξ * fourierUnitary f ξ) := by ring
  rw [h₁, h₂, sine_pair_inner, norm_mul, MellinL2.norm_fourierPhase, one_mul]
  rfl

theorem integrable_ccmActualHeadMidpointSpectralCurrent (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    Integrable (fun ξ : ℝ =>
      ccmActualHeadMidpointCurrentSymbol T N r ξ * ‖fourierUnitary f ξ‖^2) :=
  (MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    (fourierUnitary (logTranslationCLM r f - f))
    (fourierUnitary (ccmActualHeadMidpointOddField T N f r))).re.congr
      (current_integrand_ae T N f r)

/-- Exact signed spectral current, including prime interference and terminal correction. -/
theorem re_inner_increment_completed_eq_midpoint_spectral (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f - f)
      (ccmActualHeadQuantileCompletedCoherentField T N f r)).re =
      ∫ ξ : ℝ, ccmActualHeadMidpointCurrentSymbol T N r ξ * ‖fourierUnitary f ξ‖^2 := by
  rw [← re_inner_increment_midpointOdd,
    ← fourierUnitary.inner_map_map, MeasureTheory.L2.inner_def]
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    (fourierUnitary (logTranslationCLM r f - f))
    (fourierUnitary (ccmActualHeadMidpointOddField T N f r))
  calc
    _ = ∫ ξ : ℝ, RCLike.re
        (inner ℂ (fourierUnitary (logTranslationCLM r f - f) ξ)
          (fourierUnitary (ccmActualHeadMidpointOddField T N f r) ξ)) :=
      (integral_re hi).symm
    _ = _ := integral_congr_ae (current_integrand_ae T N f r)

theorem ccmActualHeadMidpointCurrentSymbol_neg (T : ℝ) (N : ℕ) (r ξ : ℝ) :
    ccmActualHeadMidpointCurrentSymbol T N r (-ξ) =
      ccmActualHeadMidpointCurrentSymbol T N r ξ := by
  simp [ccmActualHeadMidpointCurrentSymbol, ccmActualHeadMidpointSineSymbol_neg]

end RHTower
