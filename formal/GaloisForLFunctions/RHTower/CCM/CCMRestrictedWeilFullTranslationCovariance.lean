import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFormTranslation

/-!
# Full translation covariance of the restricted Weil source

The complete literal source is invariant under an aperture-fitting translation on the
whole form domain, not only on the pole-constrained sector.  The two polar coordinates
acquire reciprocal real characters, so their completed cross term is unchanged.  This
keeps the Gamma, polar, and finite-prime terms coupled before any boundary compression.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct FourierTransform

noncomputable section
namespace RHTower

/-- An aperture-fitting translation preserves the full literal Gamma--polar--prime source
quadratic on every form-domain vector. -/
theorem ccmRestrictedWeilSourceQuadratic_translate_full
    {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic b (ccmArchimedeanFormTranslate h hab u) =
      ccmRestrictedWeilSourceQuadratic a u := by
  have hab' : a.1 ≤ b.1 := by linarith [abs_nonneg h]
  obtain ⟨w, hwval⟩ := exists_ccmArchimedeanFormDomain_extension hab' u
  let v := ccmArchimedeanFormTranslate h hab u
  have hgamma :
      (∫ x, 2 * gammaHardyPhaseRate (2 * Real.pi * x) * ‖(v.1 : ℝ → ℂ) x‖ ^ 2) =
      ∫ x, 2 * gammaHardyPhaseRate (2 * Real.pi * x) * ‖(w.1 : ℝ → ℂ) x‖ ^ 2 := by
    rw [hwval]
    apply integral_congr_ae
    have hp := (ccmArchimedeanPhaseMul_coeFn h u.1).filter_mono
      (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [hp] with x hx
    change _ * ‖ccmArchimedeanPhaseMul h u.1 x‖ ^ 2 = _
    rw [hx, norm_mul, MellinL2.norm_fourierPhase, one_mul]
  have hp : ∀ t : ℝ,
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b v : SoninL2))
        (ccmArchimedeanFormToAperture b v : SoninL2) =
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b w : SoninL2))
        (ccmArchimedeanFormToAperture b w : SoninL2) := by
    intro t
    rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq hwval]
    change inner ℂ (logTranslationCLM t
      (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2))
        (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2) = _
    rw [ccmArchimedeanFormTranslate_physical]
    rw [logTranslationCLM_add_apply, add_comm t h, ← logTranslationCLM_add_apply]
    exact (MellinL2.additiveTranslationUnitary h).inner_map_map _ _
  have hminus_v := inner_polar_ccmArchimedeanFormTranslate h hab (-1 / 2) u
  have hplus_v := inner_polar_ccmArchimedeanFormTranslate h hab (1 / 2) u
  have hminus_w := inner_ccmPolarApertureVector_eq_of_val_eq hab' (-1 / 2) hwval
  have hplus_w := inner_ccmPolarApertureVector_eq_of_val_eq hab' (1 / 2) hwval
  have hscale :
      ((Real.exp (-((-1 / 2) * h)) : ℂ) * (Real.exp (-((1 / 2) * h)) : ℂ)) = 1 := by
    have hzero : -((-1 / 2) * h) + -((1 / 2) * h) = 0 := by ring
    rw [← Complex.ofReal_mul, ← Real.exp_add, hzero, Real.exp_zero]
    simp
  have hpolar :
      ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (-1 / 2))
          (ccmArchimedeanFormToAperture b v)) *
          inner ℂ (ccmPolarApertureVector b (1 / 2))
            (ccmArchimedeanFormToAperture b v) +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (1 / 2))
          (ccmArchimedeanFormToAperture b v)) *
          inner ℂ (ccmPolarApertureVector b (-1 / 2))
            (ccmArchimedeanFormToAperture b v)).re =
      ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (-1 / 2))
          (ccmArchimedeanFormToAperture b w)) *
          inner ℂ (ccmPolarApertureVector b (1 / 2))
            (ccmArchimedeanFormToAperture b w) +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (1 / 2))
          (ccmArchimedeanFormToAperture b w)) *
          inner ℂ (ccmPolarApertureVector b (-1 / 2))
            (ccmArchimedeanFormToAperture b w)).re := by
    rw [hminus_v, hplus_v, hminus_w, hplus_w]
    simp only [map_mul, Complex.conj_ofReal]
    let p : ℂ := Real.exp (-((-1 / 2) * h))
    let q : ℂ := Real.exp (-((1 / 2) * h))
    let A := inner ℂ (ccmPolarApertureVector a (-1 / 2))
      (ccmArchimedeanFormToAperture a u)
    let B := inner ℂ (ccmPolarApertureVector a (1 / 2))
      (ccmArchimedeanFormToAperture a u)
    have hpq : p * q = 1 := hscale
    have hqp : q * p = 1 := by rw [mul_comm, hpq]
    calc
      _ = ((p * q) * ((starRingEnd ℂ) A * B) +
          (q * p) * ((starRingEnd ℂ) B * A)).re := by
        dsimp only [p, q, A, B]
        ring
      _ = _ := by
        rw [hpq, hqp]
        dsimp only [A, B]
        simp
  calc
    _ = ccmRestrictedWeilSourceQuadratic b w := by
      change ccmRestrictedWeilSourceQuadratic b v = _
      unfold ccmRestrictedWeilSourceQuadratic
      dsimp only
      rw [hpolar]
      simp_rw [hp]
      rw [hgamma]
    _ = _ := ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab' hwval

end RHTower
