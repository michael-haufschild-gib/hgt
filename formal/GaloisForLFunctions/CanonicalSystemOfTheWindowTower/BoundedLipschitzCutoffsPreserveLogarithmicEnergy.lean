import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicEnergyHasItsLiteralJumpForm

/-!
# Bounded Lipschitz cutoffs preserve logarithmic energy

The translation product rule bounds the cutoff loss by the original loss
plus a term linear in the shift. The literal Lévy density integrates its
square, so every bounded Lipschitz cutoff preserves the complete form domain.
An explicit overlapping endpoint cutoff supplies interval localization.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform InnerProductSpace
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- Translation in literal physical L² coordinates. -/
theorem logarithmicTranslation_coeFn (t : ℝ) (f : RealLineL2) :
    (logTranslationCLM t f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + t) :=
  Lp.coeFn_compMeasurePreserving f (MellinL2.realTranslation_measurePreserving t)

/-- Bounded real multiplication in physical L² coordinates. -/
def logarithmicCutoffMultiplier {χ : ℝ → ℝ} (hm : Measurable χ) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) : RealLineL2 →L[ℂ] RealLineL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (Complex.continuous_ofReal.measurable.comp hm) hM
    (fun x => by simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hb x)

theorem logarithmicCutoffMultiplier_coeFn {χ : ℝ → ℝ} (hm : Measurable χ) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (f : RealLineL2) :
    (logarithmicCutoffMultiplier hm hM hb f : ℝ → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) * f x :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem norm_logarithmicCutoffMultiplier_le {χ : ℝ → ℝ} (hm : Measurable χ) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) : ‖logarithmicCutoffMultiplier hm hM hb‖ ≤ M :=
  norm_lpBoundedMulCLM_le _ _ _

/-- Real physical multiplication is symmetric in the actual L² inner product. -/
theorem inner_logarithmicCutoffMultiplier {χ : ℝ → ℝ} (hm : Measurable χ) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (f g : RealLineL2) :
    inner ℂ (logarithmicCutoffMultiplier hm hM hb f) g =
      inner ℂ f (logarithmicCutoffMultiplier hm hM hb g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [logarithmicCutoffMultiplier_coeFn hm hM hb f,
    logarithmicCutoffMultiplier_coeFn hm hM hb g] with x hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-- The physical multiplier commutator with translation gains exactly one power of the shift. -/
theorem logarithmicCutoff_translation_loss_le {χ : ℝ → ℝ} (hm : Measurable χ) {M Λ : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|) (f : RealLineL2) (t : ℝ) :
    ‖logTranslationCLM t (logarithmicCutoffMultiplier hm hM hb f) -
        logarithmicCutoffMultiplier hm hM hb f‖ ≤
      M * ‖logTranslationCLM t f - f‖ + Λ * |t| * ‖f‖ := by
  let T := logTranslationCLM t
  let P := logarithmicCutoffMultiplier hm hM hb
  let A : RealLineL2 := T (P f) - P f
  let B : RealLineL2 := P (T f - f)
  have hTnorm : ‖T f‖ = ‖f‖ := (MellinL2.additiveTranslationUnitary t).norm_map f
  have hcoef : (A - B : RealLineL2) =ᵐ[volume] fun x => ((χ (x + t) - χ x : ℝ) : ℂ) * (T f) x := by
    have hshift := (logarithmicCutoffMultiplier_coeFn hm hM hb f).comp_tendsto
      (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.tendsto_ae
    filter_upwards [Lp.coeFn_sub A B, Lp.coeFn_sub (T (P f)) (P f),
      logarithmicCutoffMultiplier_coeFn hm hM hb f,
      logarithmicCutoffMultiplier_coeFn hm hM hb (T f - f),
      Lp.coeFn_sub (T f) f, logarithmicTranslation_coeFn t (P f),
      logarithmicTranslation_coeFn t f, hshift]
      with x hAB hA hP hB hsub hTP hTf hPs
    change (P f) (x + t) = (χ (x + t) : ℂ) * f (x + t) at hPs
    rw [hAB]
    change A x - B x = _
    rw [hA, hB]
    simp only [Pi.sub_apply]
    rw [hTP, hPs, hP, hsub]
    simp only [Pi.sub_apply]
    rw [hTf]
    push_cast
    ring
  have hcomm : ‖A - B‖ ≤ Λ * |t| * ‖f‖ := by
    have hnon : 0 ≤ Λ * |t| := mul_nonneg hΛ (abs_nonneg t)
    have hn : ‖A - B‖ ≤ ‖((Λ * |t| : ℝ) : ℂ) • T f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hcoef, Lp.coeFn_smul (((Λ * |t| : ℝ) : ℂ)) (T f)] with x hx hc
      rw [hx, hc]
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hΛ, abs_abs]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [add_sub_cancel_left] using hlip (x + t) x
    simpa only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hnon, hTnorm] using hn
  have hBnorm : ‖B‖ ≤ M * ‖T f - f‖ :=
    (P.le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (norm_logarithmicCutoffMultiplier_le hm hM hb) (norm_nonneg _))
  change ‖A‖ ≤ _
  calc
    ‖A‖ ≤ ‖A - B‖ + ‖B‖ := by simpa only [sub_add_cancel] using norm_add_le (A - B) B
    _ ≤ Λ * |t| * ‖f‖ + M * ‖T f - f‖ := add_le_add hcomm hBnorm
    _ = _ := add_comm _ _

private theorem integrable_logReferenceLevyDensity_mul_sq :
    IntegrableOn (fun t : ℝ => logReferenceLevyDensity t * t ^ 2) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num)
  apply hi.mono' ((measurable_logReferenceLevyDensity.mul (measurable_id.pow_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (0 : ℝ) < t at ht
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, id_eq]
  rw [Real.norm_of_nonneg (mul_nonneg (logReferenceLevyDensity_nonneg ht.le) (sq_nonneg t))]
  calc
    _ = (t / 2) * Real.exp (-t) := by unfold logReferenceLevyDensity; field_simp [ne_of_gt ht]
    _ ≤ Real.exp (t / 2) * Real.exp (-t) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith only [Real.add_one_le_exp (t / 2)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Every bounded Lipschitz physical cutoff preserves the actual logarithmic form domain. -/
theorem hasLogarithmicEnergy_cutoff {χ : ℝ → ℝ} (hm : Measurable χ) {M Λ : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|) {f : RealLineL2}
    (hf : HasLogarithmicEnergy f) : HasLogarithmicEnergy (logarithmicCutoffMultiplier hm hM hb f) := by
  let g := logarithmicCutoffMultiplier hm hM hb f
  have hE := (hasLogarithmicEnergy_iff_integrable_jump f).mp hf
  have hbound := (hE.const_mul (2 * M ^ 2)).add
    (integrable_logReferenceLevyDensity_mul_sq.const_mul (2 * Λ ^ 2 * ‖f‖ ^ 2))
  have hc : Continuous (fun t : ℝ => logTranslationCLM t g - g) :=
    (continuous_logTranslationCLM g).sub continuous_const
  apply (hasLogarithmicEnergy_iff_integrable_jump g).mpr
  apply hbound.mono' (measurable_logReferenceLevyDensity.aestronglyMeasurable.mul
    (hc.aestronglyMeasurable.norm.pow 2))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (0 : ℝ) < t at ht
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, id_eq]
  rw [Real.norm_of_nonneg (mul_nonneg (logReferenceLevyDensity_nonneg ht.le) (sq_nonneg _))]
  have hlin := logarithmicCutoff_translation_loss_le hm hM hb hΛ hlip f t
  have hsq : ‖logTranslationCLM t g - g‖ ^ 2 ≤
      2 * M ^ 2 * ‖logTranslationCLM t f - f‖ ^ 2 + 2 * Λ ^ 2 * t ^ 2 * ‖f‖ ^ 2 := by
    calc
      _ ≤ (M * ‖logTranslationCLM t f - f‖ + Λ * |t| * ‖f‖) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hlin
      _ ≤ 2 * (M * ‖logTranslationCLM t f - f‖) ^ 2 + 2 * (Λ * |t| * ‖f‖) ^ 2 := by
        nlinarith only [sq_nonneg (M * ‖logTranslationCLM t f - f‖ - Λ * |t| * ‖f‖)]
      _ = _ := by rw [abs_of_pos ht]; ring
  have h := mul_le_mul_of_nonneg_left hsq (logReferenceLevyDensity_nonneg ht.le)
  calc
    _ ≤ logReferenceLevyDensity t *
        (2 * M ^ 2 * ‖logTranslationCLM t f - f‖ ^ 2 + 2 * Λ ^ 2 * t ^ 2 * ‖f‖ ^ 2) := h
    _ = _ := by ring

/-- A concrete left-endpoint cutoff, with overlap for gluing the two endpoint representatives. -/
def logarithmicEndpointCutoff (a x : ℝ) : ℝ := min (max (3 - (2 / a) * x) 0) 1

theorem continuous_logarithmicEndpointCutoff (a : ℝ) : Continuous (logarithmicEndpointCutoff a) := by
  unfold logarithmicEndpointCutoff
  fun_prop

theorem logarithmicEndpointCutoff_nonneg (a x : ℝ) : 0 ≤ logarithmicEndpointCutoff a x :=
  le_min (le_max_right _ _) zero_le_one

theorem logarithmicEndpointCutoff_abs_le (a x : ℝ) : |logarithmicEndpointCutoff a x| ≤ 1 := by
  rw [abs_of_nonneg (logarithmicEndpointCutoff_nonneg a x)]
  exact min_le_right _ _

theorem logarithmicEndpointCutoff_eq_one {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≤ a) :
    logarithmicEndpointCutoff a x = 1 := by
  have h := mul_le_mul_of_nonneg_left hx (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le)
  rw [div_mul_cancel₀ _ (ne_of_gt ha)] at h
  unfold logarithmicEndpointCutoff
  exact min_eq_right ((by linarith : (1 : ℝ) ≤ 3 - 2 / a * x).trans (le_max_left _ _))

theorem logarithmicEndpointCutoff_eq_zero {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 3 * a / 2 ≤ x) :
    logarithmicEndpointCutoff a x = 0 := by
  have h := mul_le_mul_of_nonneg_left hx (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le)
  have he : (2 / a) * (3 * a / 2) = 3 := by field_simp [ne_of_gt ha]
  rw [he] at h
  unfold logarithmicEndpointCutoff
  rw [max_eq_right (by linarith : 3 - 2 / a * x ≤ 0), min_eq_left zero_le_one]

theorem logarithmicEndpointCutoff_lipschitz {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    |logarithmicEndpointCutoff a x - logarithmicEndpointCutoff a y| ≤ (2 / a) * |x - y| := by
  have hc : LipschitzWith 1 (fun x : ℝ => min (max x 0) 1) :=
    (LipschitzWith.id.max_const 0).min_const 1
  have h := hc.dist_le_mul (3 - (2 / a) * x) (3 - (2 / a) * y)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  change |min (max (3 - 2 / a * x) 0) 1 - min (max (3 - 2 / a * y) 0) 1| ≤ _
  refine h.trans_eq ?_
  rw [show (3 - 2 / a * x) - (3 - 2 / a * y) = -(2 / a) * (x - y) by ring,
    abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le)]

#print axioms logarithmicTranslation_coeFn
#print axioms logarithmicCutoff_translation_loss_le
#print axioms hasLogarithmicEnergy_cutoff

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
