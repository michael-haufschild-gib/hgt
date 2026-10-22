import GaloisForLFunctions.RHTower.CCM.CCMGammaLogTranslationControl

/-!
# Aperture-independent equicontinuity of complete Gamma heads

The modulus uses physical mass plus the higher Binet energy. It controls
the autocorrelation of the whole vector, including all mixed terms, without
a polynomial degree or a frequency cutoff.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- One translation radius controls every actual Gamma head, at every aperture. -/
theorem exists_ccmGammaAutocorrelation_uniform_modulus (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : SuzukiPositiveAperture)
      (u : CCMArchimedeanFormDomain a) (h s : ℝ), |h - s| < δ →
      |ccmActualHeadSymmetricAutocorrelation h (ccmArchimedeanFormToAperture a u).1 -
        ccmActualHeadSymmetricAutocorrelation s (ccmArchimedeanFormToAperture a u).1| ≤
      ε * (‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (ccmArchimedeanFormToAperture a u).1) := by
  let B : ℝ := 8 * Real.exp (5 / 2)
  let A : ℝ := B / ε ^ 2 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨Real.exp (-A) / 2, by positivity, ?_⟩
  intro a u h s hhs
  let f := ccmArchimedeanFormToAperture a u
  let H := ccmActualHeadGammaHigherBinetModeEnergy f.1
  have hH : 0 ≤ H := ccmActualHeadGammaHigherBinetModeEnergy_nonneg _
  by_cases hz : h - s = 0
  · have : h = s := sub_eq_zero.mp hz
    subst h
    simp only [sub_self, abs_zero]
    exact mul_nonneg hε.le (add_nonneg (sq_nonneg _) hH)
  have hr : 0 < |h - s| := abs_pos.mpr hz
  have hr1 : 2 * |h - s| < 1 := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hA)
    linarith
  have hl : A ≤ Real.log (1 / (2 * |h - s|)) := by
    have hlog := Real.log_le_log (by positivity : 0 < 2 * |h - s|)
      (show 2 * |h - s| ≤ Real.exp (-A) by linarith)
    rw [Real.log_exp] at hlog
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one]
    linarith
  have hD := ccmActualHeadTranslationDefect_log_bound a u ⟨1, by norm_num⟩
    ⟨|h - s|, hr, hr1⟩
  simp only [mul_one] at hD
  change Real.log (1 / (2 * |h - s|)) *
    ccmActualHeadTranslationDefect |h - s| f.1 ≤ B * H at hD
  rw [ccmActualHeadTranslationDefect_abs] at hD
  let D := ccmActualHeadTranslationDefect (h - s) f.1
  have hD0 : 0 ≤ D := by dsimp [D, ccmActualHeadTranslationDefect]; positivity
  have hAD : A * D ≤ B * H :=
    (mul_le_mul_of_nonneg_right hl hD0).trans hD
  have hAeps : A * ε ^ 2 = B + ε ^ 2 := by
    dsimp [A]
    field_simp
  have hDE : D ≤ ε ^ 2 * H := by
    have hh := mul_le_mul_of_nonneg_right hAD (sq_nonneg ε)
    have heq := congrArg (fun x : ℝ => x * D) hAeps
    have hE := mul_nonneg (sq_nonneg ε) hD0
    nlinarith only [hh, heq, hE, hB]
  have hsqrt : Real.sqrt D ≤ ε * Real.sqrt H := by
    have hd := Real.sq_sqrt hD0
    have hh := Real.sq_sqrt hH
    have hp : 0 ≤ ε * Real.sqrt H := mul_nonneg hε.le (Real.sqrt_nonneg _)
    nlinarith only [hDE, hd, hh, hp, Real.sqrt_nonneg D]
  have hcorr := abs_ccmActualHeadSymmetricAutocorrelation_sub_le_norm_mul_sqrt_defect h s f.1
  have hc := hcorr.trans (mul_le_mul_of_nonneg_left hsqrt (norm_nonneg f.1))
  have hm : ‖f‖ * Real.sqrt H ≤ ‖f‖ ^ 2 + H := by
    nlinarith [sq_nonneg (‖f‖ - Real.sqrt H), Real.sq_sqrt hH, sq_nonneg ‖f‖]
  change _ ≤ ε * (‖f‖ ^ 2 + H)
  change _ ≤ ‖f‖ * (ε * Real.sqrt H) at hc
  calc
    _ ≤ ‖f‖ * (ε * Real.sqrt H) := hc
    _ = ε * (‖f‖ * Real.sqrt H) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm hε.le

end RHTower
