import GaloisForLFunctions.RHTower.CHMDBoundedContinuousSource

/-! # Compactly cut translations of any continuous BV profile

Both the full arithmetic graph and its bounded continuous representatives
vary continuously. This supplies literal graph-valued kernels for positive
regularization and approximation of compact source targets.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry

def cutoffTranslate (χ f : ℝ → ℝ) (t x : ℝ) : ℝ := χ x * f (t - x)

theorem variation_reflected_translate_le (f : ℝ → ℝ) (t : ℝ) :
    eVariationOn (fun x => f (t - x)) univ ≤ eVariationOn f univ :=
  eVariationOn.comp_le_of_antitoneOn f (fun x => t - x)
    (fun _ _ _ _ h => sub_le_sub_left h t) (fun _ _ => mem_univ _)

theorem bv_reflected_translate {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (t : ℝ) :
    BoundedVariationOn (fun x => f (t - x)) univ :=
  ne_top_of_le_ne_top hf (variation_reflected_translate_le f t)

theorem cutoffTranslate_bv {χ f : ℝ → ℝ}
    (hχ : BoundedVariationOn χ univ) (hf : BoundedVariationOn f univ) (t : ℝ) :
    BoundedVariationOn (cutoffTranslate χ f t) univ :=
  boundedVariationOn_mul hχ (bv_reflected_translate hf t)

theorem cutoffTranslate_compact {χ : ℝ → ℝ} (hχ : HasCompactSupport χ)
    (f : ℝ → ℝ) (t : ℝ) : HasCompactSupport (cutoffTranslate χ f t) := hχ.mul_right

theorem cutoffTranslate_continuous {χ f : ℝ → ℝ}
    (hχ : Continuous χ) (hf : Continuous f) (t : ℝ) :
    Continuous (cutoffTranslate χ f t) := hχ.mul (hf.comp (continuous_const.sub continuous_id))

theorem cutoffTranslate_joint {χ f : ℝ → ℝ} (hχ : Continuous χ) (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => cutoffTranslate χ f p.1 p.2) :=
  (hχ.comp continuous_snd).mul (hf.comp (continuous_fst.sub continuous_snd))

theorem cutoffTranslate_variation_le {χ f : ℝ → ℝ}
    (hχ : BoundedVariationOn χ univ) (hf : BoundedVariationOn f univ) (t : ℝ) :
    (eVariationOn (cutoffTranslate χ f t) univ).toReal ≤
      (‖χ 0‖ + (eVariationOn χ univ).toReal) * (eVariationOn f univ).toReal +
        (‖f 0‖ + (eVariationOn f univ).toReal) * (eVariationOn χ univ).toReal := by
  let A := ‖χ 0‖ + (eVariationOn χ univ).toReal
  let B := ‖f 0‖ + (eVariationOn f univ).toReal
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eVariationOn_mul_le_of_bounds hχ (bv_reflected_translate hf t) hA hB
      (fun x _ => norm_le_of_boundedVariation_univ hχ x)
      (fun x _ => norm_le_of_boundedVariation_univ hf (t - x)))
  rw [ENNReal.toReal_ofReal (add_nonneg (mul_nonneg hA ENNReal.toReal_nonneg)
    (mul_nonneg hB ENNReal.toReal_nonneg))] at h
  have ht := ENNReal.toReal_mono hf (variation_reflected_translate_le f t)
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left ht hA) le_rfl)

theorem cutoffTranslate_zero_outside {χ f : ℝ → ℝ} (t x : ℝ) (hx : x ∉ tsupport χ) :
    cutoffTranslate χ f t x = 0 := by
  have hzero : χ x = 0 := by
    by_contra h
    exact hx (subset_tsupport χ h)
  simp only [cutoffTranslate, hzero, zero_mul]

def cutoffTranslateGraph (χ f : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hf : BoundedVariationOn f univ) (t : ℝ) : SourceGraph :=
  bvLift (cutoffTranslate χ f t) (cutoffTranslate_bv hχ hf t)

theorem continuous_cutoffTranslateGraph (χ f : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hf : BoundedVariationOn f univ)
    (hχcont : Continuous χ) (hfcont : Continuous f) (hχc : HasCompactSupport χ) :
    Continuous (cutoffTranslateGraph χ f hχ hf) := by
  apply continuous_bvLift_of_common_compact (fun t => cutoffTranslate_bv hχ hf t)
    (fun t => cutoffTranslate_compact hχc f t) (cutoffTranslate_joint hχcont hfcont)
    hχc (fun t x hx => cutoffTranslate_zero_outside t x hx)
  exact cutoffTranslate_variation_le hχ hf

def cutoffTranslateBCF (χ f : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hf : BoundedVariationOn f univ)
    (hχcont : Continuous χ) (hfcont : Continuous f) (t : ℝ) : ℝ →ᵇ ℝ :=
  bvContinuousFunction (cutoffTranslate χ f t) (cutoffTranslate_continuous hχcont hfcont t)
    (cutoffTranslate_bv hχ hf t)

theorem continuous_cutoffTranslateBCF (χ f : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hf : BoundedVariationOn f univ)
    (hχcont : Continuous χ) (hfcont : Continuous f) (hχc : HasCompactSupport χ) :
    Continuous (cutoffTranslateBCF χ f hχ hf hχcont hfcont) :=
  continuous_bvContinuousFunction_of_common_compact
    (cutoffTranslate_continuous hχcont hfcont) (cutoffTranslate_bv hχ hf)
    (cutoffTranslate_joint hχcont hfcont) hχc
    (fun t x hx => cutoffTranslate_zero_outside t x hx)

theorem cutoffTranslateGraph_source_bcf (χ f : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hf : BoundedVariationOn f univ)
    (hχcont : Continuous χ) (hfcont : Continuous f) (t : ℝ) :
    sourceMap (cutoffTranslateGraph χ f hχ hf t) =
      BoundedContinuousFunction.toLp 2 massMeasure ℝ
        (cutoffTranslateBCF χ f hχ hf hχcont hfcont t) :=
  sourceMap_bvLift_eq_bcfToLp _ _ _

end RHTower.CHMDDoobGraph
