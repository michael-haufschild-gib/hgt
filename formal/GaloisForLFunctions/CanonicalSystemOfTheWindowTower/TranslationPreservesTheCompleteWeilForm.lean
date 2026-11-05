import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ThePrecontactWeilSpacesHaveEntireFourierCoordinates
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFormTranslation

/-!
# Translation preserves the complete unshifted Weil form

The two polar coordinates acquire reciprocal exponential factors. They
cancel in the full polar pairing, so translation preserves the actual Weil
form without a polar constraint. Before contact this gives exact Hilbert
isometries between apertures with sufficient support margin.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower

/-- Translation preserves the full literal source quadratic, including both polar coordinates. -/
theorem completeWeilSourceQuadratic_translate {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1+|h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic b (ccmArchimedeanFormTranslate h hab u) =
      ccmRestrictedWeilSourceQuadratic a u := by
  have hab' : a.1 ≤ b.1 := by linarith only [hab, abs_nonneg h]
  obtain ⟨w, hw⟩ := exists_ccmArchimedeanFormDomain_extension hab' u
  let v := ccmArchimedeanFormTranslate h hab u
  have hgamma :
      (∫ x, 2*gammaHardyPhaseRate (2*Real.pi*x)*‖(v.1 : ℝ → ℂ) x‖^2) =
      ∫ x, 2*gammaHardyPhaseRate (2*Real.pi*x)*‖(w.1 : ℝ → ℂ) x‖^2 := by
    rw [hw]
    apply integral_congr_ae
    have hp := (ccmArchimedeanPhaseMul_coeFn h u.1).filter_mono
      (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [hp] with x hx
    change _*‖ccmArchimedeanPhaseMul h u.1 x‖^2 = _
    rw [hx, norm_mul, MellinL2.norm_fourierPhase, one_mul]
  have hprime (t : ℝ) :
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b v : SoninL2))
        (ccmArchimedeanFormToAperture b v : SoninL2) =
      inner ℂ (logTranslationCLM t (ccmArchimedeanFormToAperture b w : SoninL2))
        (ccmArchimedeanFormToAperture b w : SoninL2) := by
    rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq hw]
    change inner ℂ (logTranslationCLM t
      (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2))
        (ccmArchimedeanFormToAperture b (ccmArchimedeanFormTranslate h hab u) : SoninL2) = _
    rw [ccmArchimedeanFormTranslate_physical, logTranslationCLM_add_apply,
      add_comm t h, ← logTranslationCLM_add_apply]
    exact (MellinL2.additiveTranslationUnitary h).inner_map_map _ _
  have hpolar (s : ℝ) :
      inner ℂ (ccmPolarApertureVector b s) (ccmArchimedeanFormToAperture b v) =
        (Real.exp (-s*h) : ℂ)*
          inner ℂ (ccmPolarApertureVector b s) (ccmArchimedeanFormToAperture b w) := by
    rw [inner_ccmPolarApertureVector_eq_of_val_eq hab' s hw]
    exact inner_polar_ccmArchimedeanFormTranslate h hab s u
  have hexp : (Real.exp (-(-1/2)*h) : ℂ)*(Real.exp (-(1/2)*h) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -(-1/2 : ℝ)*h + -(1/2 : ℝ)*h = 0 by ring,
      Real.exp_zero, Complex.ofReal_one]
  have hpolareq :
      ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (-1/2)) (ccmArchimedeanFormToAperture b v))*
        inner ℂ (ccmPolarApertureVector b (1/2)) (ccmArchimedeanFormToAperture b v) +
      (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (1/2)) (ccmArchimedeanFormToAperture b v))*
        inner ℂ (ccmPolarApertureVector b (-1/2)) (ccmArchimedeanFormToAperture b v)) =
      ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (-1/2)) (ccmArchimedeanFormToAperture b w))*
        inner ℂ (ccmPolarApertureVector b (1/2)) (ccmArchimedeanFormToAperture b w) +
      (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (1/2)) (ccmArchimedeanFormToAperture b w))*
        inner ℂ (ccmPolarApertureVector b (-1/2)) (ccmArchimedeanFormToAperture b w)) := by
    rw [hpolar, hpolar]
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination
      ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (-1/2)) (ccmArchimedeanFormToAperture b w))*
        inner ℂ (ccmPolarApertureVector b (1/2)) (ccmArchimedeanFormToAperture b w) +
      (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (1/2)) (ccmArchimedeanFormToAperture b w))*
        inner ℂ (ccmPolarApertureVector b (-1/2)) (ccmArchimedeanFormToAperture b w))*hexp
  calc
    _ = ccmRestrictedWeilSourceQuadratic b w := by
      change ccmRestrictedWeilSourceQuadratic b v = _
      dsimp only [ccmRestrictedWeilSourceQuadratic]
      rw [hgamma, hpolareq]
      simp_rw [hprime]
    _ = _ := ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab' hw

namespace WeilHilbertBeforeContact

/-- Physical translation is an exact Weil isometry whenever the translated support fits. -/
def translate {a b : PrecontactAperture} (h : ℝ) (hab : a.1.1+|h| ≤ b.1.1) :
    WeilHilbertBeforeContact a →ₗᵢ[ℂ] WeilHilbertBeforeContact b where
  toLinearMap := (toForm b).symm.toLinearMap.comp
    ((ccmArchimedeanFormTranslate h hab).toLinearMap.comp (toForm a).toLinearMap)
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_weil, norm_sq_eq_weil]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    rw [ccmRestrictedWeilForm_self_re_eq_source, ccmRestrictedWeilForm_self_re_eq_source]
    exact completeWeilSourceQuadratic_translate h hab (toForm a u)

/-- The Hilbert isometry acts by the literal physical translation. -/
theorem physical_translate {a b : PrecontactAperture} (h : ℝ)
    (hab : a.1.1+|h| ≤ b.1.1) (u : WeilHilbertBeforeContact a) :
    ccmArchimedeanFormEmbedding b.1 (toForm b (translate h hab u)) =
      logTranslationCLM h (ccmArchimedeanFormEmbedding a.1 (toForm a u)) := by
  change ccmArchimedeanFormEmbedding b.1
    (toForm b ((toForm b).symm (ccmArchimedeanFormTranslate h hab (toForm a u)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact ccmArchimedeanFormTranslate_physical h hab (toForm a u)

/-- Physical translation multiplies the entire Fourier coordinate by its exact exponential character. -/
theorem fourier_translate {a b : PrecontactAperture} (h : ℝ)
    (hab : a.1.1+|h| ≤ b.1.1) (u : WeilHilbertBeforeContact a) (z : ℂ) :
    fourier b (translate h hab u) z = Complex.exp (-I*z*(h : ℂ))*fourier a u z := by
  rw [fourier_eq_whole, fourier_eq_whole]
  have hcut {c : PrecontactAperture} (v : WeilHilbertBeforeContact c) :
      suzukiCutoff c.1.1 (ccmArchimedeanFormToAperture c.1 (toForm c v) : SoninL2) =
        (ccmArchimedeanFormToAperture c.1 (toForm c v) : SoninL2) :=
    indicatorCutoff_suzukiApertureHilbert c.1 _
  unfold suzukiCompactL2Fourier
  change (∫ x : ℝ, (suzukiCutoff b.1.1
      (ccmArchimedeanFormToAperture b.1 (toForm b (translate h hab u)) : SoninL2)) x *
        Complex.exp (I*z*(x : ℂ))) =
    Complex.exp (-I*z*(h : ℂ)) * ∫ x : ℝ, (suzukiCutoff a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a u) : SoninL2)) x * Complex.exp (I*z*(x : ℂ))
  rw [hcut, hcut]
  change (∫ x : ℝ, ccmArchimedeanFormEmbedding b.1 (toForm b (translate h hab u)) x *
      Complex.exp (I*z*(x : ℂ))) = _
  rw [physical_translate]
  let f := ccmArchimedeanFormEmbedding a.1 (toForm a u)
  calc
    _ = ∫ x : ℝ, f (x+h)*Complex.exp (I*z*((x+h-h : ℝ) : ℂ)) := by
      apply integral_congr_ae
      have ht : (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume] fun x => f (x+h) :=
        Lp.coeFn_compMeasurePreserving f (MellinL2.realTranslation_measurePreserving h)
      filter_upwards [ht] with x hx
      rw [hx, add_sub_cancel_right]
    _ = ∫ x : ℝ, f x*Complex.exp (I*z*((x-h : ℝ) : ℂ)) :=
      integral_add_right_eq_self (fun x : ℝ => f x*Complex.exp (I*z*((x-h : ℝ) : ℂ))) h
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      change f x*Complex.exp (I*z*((x-h : ℝ) : ℂ)) =
        Complex.exp (-I*z*(h : ℂ))*(f x*Complex.exp (I*z*(x : ℂ)))
      rw [show I*z*((x-h : ℝ) : ℂ) = -I*z*(h : ℂ)+I*z*(x : ℂ) by push_cast; ring,
        Complex.exp_add]
      ring

#print axioms translate
#print axioms physical_translate
#print axioms fourier_translate
end WeilHilbertBeforeContact
#print axioms completeWeilSourceQuadratic_translate
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
