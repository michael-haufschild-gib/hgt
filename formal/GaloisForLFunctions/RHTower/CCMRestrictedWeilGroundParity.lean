import GaloisForLFunctions.RHTower.CCMRestrictedWeilFriedrichsOperator
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# Reflection grading of the exact restricted Weil ground

The literal archimedean weight, polar pair, and symmetric finite-prime translations are all
reflection invariant.  This file lifts physical reflection to the complete weighted form domain
and splits an attained ground vector into pure parity ground vectors.  Thus mixed-parity escape is
not an independent Route O ground channel.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct BigOperators

noncomputable section

namespace RHTower

private theorem map_withDensity_measurableEquiv' {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (e : α ≃ᵐ β) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext t ht
  rw [withDensity_apply _ ht, Measure.restrict_map e.measurable ht]
  rw [show (∫⁻ y : β, f (e.symm y) ∂(Measure.map (⇑e) (μ.restrict (⇑e ⁻¹' t))))
      = ∫⁻ x : α, f (e.symm (e x)) ∂(μ.restrict (⇑e ⁻¹' t)) from
    lintegral_map (hf.comp e.symm.measurable) e.measurable]
  simp only [MeasurableEquiv.symm_apply_apply]
  rw [Measure.map_apply e.measurable ht, withDensity_apply _ (e.measurable ht)]

@[simp] theorem ccmArchimedeanFormWeight_neg (x : ℝ) :
    ccmArchimedeanFormWeight (-x) = ccmArchimedeanFormWeight x := by
  simp [ccmArchimedeanFormWeight]

theorem ccmArchimedeanFormMeasure_map_neg :
    ccmArchimedeanFormMeasure.map (fun x : ℝ => -x) =
      ccmArchimedeanFormMeasure := by
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.neg ℝ
  have hdensity : Measurable (fun xi : ℝ =>
      (Real.toNNReal (ccmArchimedeanFormWeight xi) : ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp measurable_ccmArchimedeanFormWeightNNReal
  rw [show (fun x : ℝ => -x) = e from rfl]
  rw [ccmArchimedeanFormMeasure,
    map_withDensity_measurableEquiv' volume e hdensity]
  change ((volume.map (fun x : ℝ => -x)).withDensity
      (fun y => (Real.toNNReal (ccmArchimedeanFormWeight (-y)) : ℝ≥0∞))) = _
  rw [(Measure.measurePreserving_neg (volume : Measure ℝ)).map_eq]
  congr 1
  funext x
  rw [ccmArchimedeanFormWeight_neg]

theorem ccmArchimedeanFormMeasure_measurePreserving_neg :
    MeasurePreserving (fun x : ℝ => -x)
      ccmArchimedeanFormMeasure ccmArchimedeanFormMeasure :=
  ⟨measurable_neg, ccmArchimedeanFormMeasure_map_neg⟩

/-- Reflection on the exact weighted archimedean Fourier form space. -/
def ccmArchimedeanFourierReflection :
    CCMArchimedeanFourierL2 →ₗᵢ[ℂ] CCMArchimedeanFourierL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x)
    ccmArchimedeanFormMeasure_measurePreserving_neg

theorem ccmArchimedeanFourierReflection_ae (f : CCMArchimedeanFourierL2) :
    ccmArchimedeanFourierReflection f =ᵐ[ccmArchimedeanFormMeasure]
      fun x : ℝ => f (-x) :=
  Lp.coeFn_compMeasurePreserving f ccmArchimedeanFormMeasure_measurePreserving_neg

@[simp] theorem ccmArchimedeanFourierReflection_involutive
    (f : CCMArchimedeanFourierL2) :
    ccmArchimedeanFourierReflection (ccmArchimedeanFourierReflection f) = f := by
  apply Lp.ext
  have hinner := (ccmArchimedeanFourierReflection_ae f).comp_tendsto
    ccmArchimedeanFormMeasure_measurePreserving_neg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [ccmArchimedeanFourierReflection_ae
    (ccmArchimedeanFourierReflection f), hinner] with x hout hin
  rw [hout]
  simpa [Function.comp_apply] using hin

theorem ccmArchimedeanWeightedToL2_reflection
    (f : CCMArchimedeanFourierL2) :
    ccmArchimedeanWeightedToL2 (ccmArchimedeanFourierReflection f) =
      l2Reflection (ccmArchimedeanWeightedToL2 f) := by
  apply Lp.ext
  have href := (ccmArchimedeanFourierReflection_ae f).filter_mono
    (ae_mono volume_le_ccmArchimedeanFormMeasure)
  have hweightedNeg := (ccmArchimedeanWeightedToL2_coeFn f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn
      (ccmArchimedeanFourierReflection f), href,
    l2Reflection_ae (ccmArchimedeanWeightedToL2 f), hweightedNeg] with
      x hout hrefx hright hin
  rw [hout, hrefx, hright]
  simpa [Function.comp_apply] using hin.symm

theorem ccmArchimedeanFourierToTime_reflection
    (f : CCMArchimedeanFourierL2) :
    ccmArchimedeanFourierToTime (ccmArchimedeanFourierReflection f) =
      l2Reflection (ccmArchimedeanFourierToTime f) := by
  apply fourierUnitary.injective
  rw [fourierUnitary_ccmArchimedeanFourierToTime,
    fourierUnitary_l2Reflection, fourierUnitary_ccmArchimedeanFourierToTime,
    ccmArchimedeanWeightedToL2_reflection]

/-- Reflection lifted to the exact complete restricted-Weil form domain. -/
def ccmArchimedeanFormReflection (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →ₗᵢ[ℂ] CCMArchimedeanFormDomain a where
  toFun f := ⟨ccmArchimedeanFourierReflection f.1, by
    rw [LinearMap.mem_ker]
    have hf := f.property
    rw [LinearMap.mem_ker] at hf
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (ccmArchimedeanFourierToTime f.1) = 0 at hf
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (ccmArchimedeanFourierToTime
          (ccmArchimedeanFourierReflection f.1)) = 0
    rw [ccmArchimedeanFourierToTime_reflection, sub_apply, one_apply_eq_self,
      ← l2Reflection_indicatorCutoff_central]
    have hcut : indicatorCutoff (centralInterval a.1)
        (measurableSet_centralInterval a.1)
          (ccmArchimedeanFourierToTime f.1) =
        ccmArchimedeanFourierToTime f.1 := (sub_eq_zero.mp hf).symm
    rw [hcut]
    exact sub_self _⟩
  map_add' f g := Subtype.ext (map_add ccmArchimedeanFourierReflection f.1 g.1)
  map_smul' c f := Subtype.ext (map_smul ccmArchimedeanFourierReflection c f.1)
  norm_map' f := ccmArchimedeanFourierReflection.norm_map f.1

@[simp] theorem ccmArchimedeanFormReflection_involutive
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormReflection a (ccmArchimedeanFormReflection a f) = f := by
  exact Subtype.ext (ccmArchimedeanFourierReflection_involutive f.1)

theorem ccmArchimedeanFormToAperture_reflection
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ((ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a f) :
        suzukiApertureHilbert a) : SoninL2) =
      l2Reflection ((ccmArchimedeanFormToAperture a f :
        suzukiApertureHilbert a) : SoninL2) := by
  exact ccmArchimedeanFourierToTime_reflection f.1

theorem l2Reflection_logTranslationCLM (h : ℝ) (f : SoninL2) :
    l2Reflection (logTranslationCLM h f) =
      logTranslationCLM (-h) (l2Reflection f) := by
  change l2Reflection
      (Lp.compMeasurePreserving (MellinL2.realTranslationEquiv h)
        (MellinL2.realTranslation_measurePreserving h) f) =
    Lp.compMeasurePreserving (MellinL2.realTranslationEquiv (-h))
      (MellinL2.realTranslation_measurePreserving (-h)) (l2Reflection f)
  apply Lp.ext
  have htransNeg := (Lp.coeFn_compMeasurePreserving f
      (MellinL2.realTranslation_measurePreserving h)).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hrefTrans := (l2Reflection_ae f).comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-h)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae
      (Lp.compMeasurePreserving (MellinL2.realTranslationEquiv h)
        (MellinL2.realTranslation_measurePreserving h) f), htransNeg,
    Lp.coeFn_compMeasurePreserving (l2Reflection f)
      (MellinL2.realTranslation_measurePreserving (-h)), hrefTrans] with
      x hleft hfirst hright hsecond
  have hfirst' :
      Lp.compMeasurePreserving (MellinL2.realTranslationEquiv h)
        (MellinL2.realTranslation_measurePreserving h) f (-x) = f (-x + h) := by
    simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hfirst
  have hright' :
      Lp.compMeasurePreserving (MellinL2.realTranslationEquiv (-h))
        (MellinL2.realTranslation_measurePreserving (-h)) (l2Reflection f) x =
      l2Reflection f (x + -h) := by
    simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hright
  have hsecond' : l2Reflection f (x + -h) = f (h - x) := by
    have hraw : l2Reflection f (x + -h) = f (h + -x) := by
      simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hsecond
    convert hraw using 1 <;> ring
  rw [hleft, hfirst', hright', hsecond']
  congr 1 <;> ring

@[simp] theorem l2Reflection_ccmPolarL2Vector
    (a : SuzukiPositiveAperture) (s : ℝ) :
    l2Reflection (ccmPolarL2Vector a s) = ccmPolarL2Vector a (-s) := by
  apply Lp.ext
  have hpolarNeg := (ccmPolarL2Vector_coeFn a s).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (ccmPolarL2Vector a s), hpolarNeg,
    ccmPolarL2Vector_coeFn a (-s)] with x hleft hneg hright
  rw [hleft, hright]
  have hneg' : ccmPolarL2Vector a s (-x) =
      (centralInterval a.1).indicator (ccmPolarProfile s) (-x) := by
    simpa [Function.comp_apply] using hneg
  rw [hneg']
  by_cases hx : x ∈ centralInterval a.1
  · have hnx := (neg_mem_centralInterval_iff a.1 x).2 hx
    rw [Set.indicator_of_mem hnx, Set.indicator_of_mem hx]
    simp [ccmPolarProfile]
  · have hnx : -x ∉ centralInterval a.1 :=
      mt (neg_mem_centralInterval_iff a.1 x).1 hx
    rw [Set.indicator_of_notMem hnx, Set.indicator_of_notMem hx]

theorem inner_ccmPolarL2Vector_reflection
    (a : SuzukiPositiveAperture) (s : ℝ) (f : SoninL2) :
    inner ℂ (ccmPolarL2Vector a s) (l2Reflection f) =
      inner ℂ (ccmPolarL2Vector a (-s)) f := by
  rw [← l2Reflection_ccmPolarL2Vector]
  exact (l2Reflection_symmetric _ _).symm

@[simp] theorem ccmPolarApertureVector_coe
    (a : SuzukiPositiveAperture) (s : ℝ) :
    ((ccmPolarApertureVector a s : suzukiApertureHilbert a) : SoninL2) =
      ccmPolarL2Vector a s := by
  rfl

theorem inner_logTranslationCLM_reflection
    (h : ℝ) (f : SoninL2) :
    inner ℂ (logTranslationCLM h (l2Reflection f)) (l2Reflection f) =
      inner ℂ (logTranslationCLM (-h) f) f := by
  have htransport : logTranslationCLM h (l2Reflection f) =
      l2Reflection (logTranslationCLM (-h) f) := by
    simpa using (l2Reflection_logTranslationCLM (-h) f).symm
  rw [htransport]
  exact l2ReflectionIsometry.inner_map_map _ _

theorem inner_ccmFinitePrimeOperator_reflection
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    let q := ccmArchimedeanFormToAperture a f
    let qr := ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a f)
    inner ℂ (ccmFinitePrimeOperator a qr) qr =
      inner ℂ (ccmFinitePrimeOperator a q) q := by
  dsimp only
  rw [inner_ccmFinitePrimeOperator, inner_ccmFinitePrimeOperator]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [inner_ccmPrimeTransportOperator, inner_ccmPrimeTransportOperator]
  rw [show ((ccmArchimedeanFormToAperture a
      (ccmArchimedeanFormReflection a f) : suzukiApertureHilbert a) : SoninL2) =
        l2Reflection ((ccmArchimedeanFormToAperture a f :
          suzukiApertureHilbert a) : SoninL2) from
    ccmArchimedeanFormToAperture_reflection a f]
  rw [inner_logTranslationCLM_reflection, inner_logTranslationCLM_reflection]
  ring

theorem inner_ccmPolarOperator_reflection
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    let q := ccmArchimedeanFormToAperture a f
    let qr := ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a f)
    inner ℂ (ccmPolarOperator a qr) qr = inner ℂ (ccmPolarOperator a q) q := by
  dsimp only
  rw [inner_ccmPolarOperator, inner_ccmPolarOperator]
  change (starRingEnd ℂ)
      (inner ℂ (ccmPolarL2Vector a (-1 / 2))
        (ccmArchimedeanFormToAperture a
          (ccmArchimedeanFormReflection a f)).1) *
      inner ℂ (ccmPolarL2Vector a (1 / 2))
        (ccmArchimedeanFormToAperture a
          (ccmArchimedeanFormReflection a f)).1 +
      (starRingEnd ℂ)
      (inner ℂ (ccmPolarL2Vector a (1 / 2))
        (ccmArchimedeanFormToAperture a
          (ccmArchimedeanFormReflection a f)).1) *
      inner ℂ (ccmPolarL2Vector a (-1 / 2))
        (ccmArchimedeanFormToAperture a
          (ccmArchimedeanFormReflection a f)).1 = _
  rw [show (ccmArchimedeanFormToAperture a
      (ccmArchimedeanFormReflection a f)).1 =
        l2Reflection ((ccmArchimedeanFormToAperture a f :
          suzukiApertureHilbert a) : SoninL2) from
    ccmArchimedeanFormToAperture_reflection a f]
  rw [inner_ccmPolarL2Vector_reflection, inner_ccmPolarL2Vector_reflection]
  norm_num
  ring

theorem inner_ccmRestrictedWeilBoundedRemainder_reflection
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    let q := ccmArchimedeanFormToAperture a f
    let qr := ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a f)
    inner ℂ (ccmRestrictedWeilBoundedRemainder a qr) qr =
      inner ℂ (ccmRestrictedWeilBoundedRemainder a q) q := by
  dsimp only
  rw [inner_ccmRestrictedWeilBoundedRemainder,
    inner_ccmRestrictedWeilBoundedRemainder,
    inner_ccmPolarOperator_reflection,
    inner_ccmFinitePrimeOperator_reflection]
  have hphysical :
      inner ℂ (ccmArchimedeanFormToAperture a
          (ccmArchimedeanFormReflection a f))
          (ccmArchimedeanFormToAperture a
            (ccmArchimedeanFormReflection a f)) =
        inner ℂ (ccmArchimedeanFormToAperture a f)
          (ccmArchimedeanFormToAperture a f) := by
    change inner ℂ
      (ccmArchimedeanFormToAperture a
        (ccmArchimedeanFormReflection a f)).1
      (ccmArchimedeanFormToAperture a
        (ccmArchimedeanFormReflection a f)).1 = _
    rw [show (ccmArchimedeanFormToAperture a
        (ccmArchimedeanFormReflection a f)).1 =
          l2Reflection ((ccmArchimedeanFormToAperture a f :
            suzukiApertureHilbert a) : SoninL2) from
      ccmArchimedeanFormToAperture_reflection a f]
    exact l2ReflectionIsometry.inner_map_map _ _
  rw [hphysical]

/-- The exact restricted Weil quadratic is invariant under physical reflection on its complete
form domain. -/
@[simp] theorem ccmRestrictedWeilSourceQuadratic_reflection
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormReflection a f) =
      ccmRestrictedWeilSourceQuadratic a f := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source,
    ← ccmRestrictedWeilForm_self_re_eq_source]
  unfold ccmRestrictedWeilForm
  rw [Complex.add_re, Complex.add_re,
    inner_ccmRestrictedWeilBoundedRemainder_reflection]
  have hform : inner ℂ (ccmArchimedeanFormReflection a f)
      (ccmArchimedeanFormReflection a f) = inner ℂ f f :=
    (ccmArchimedeanFormReflection a).inner_map_map f f
  rw [hform]

/-- Reflection-even component of a complete restricted-Weil form vector. -/
def ccmRestrictedWeilEvenPart (a : SuzukiPositiveAperture)
    (f : CCMArchimedeanFormDomain a) : CCMArchimedeanFormDomain a :=
  (2 : ℂ)⁻¹ • (f + ccmArchimedeanFormReflection a f)

/-- Reflection-odd component of a complete restricted-Weil form vector. -/
def ccmRestrictedWeilOddPart (a : SuzukiPositiveAperture)
    (f : CCMArchimedeanFormDomain a) : CCMArchimedeanFormDomain a :=
  (2 : ℂ)⁻¹ • (f - ccmArchimedeanFormReflection a f)

@[simp] theorem ccmArchimedeanFormReflection_evenPart
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormReflection a (ccmRestrictedWeilEvenPart a f) =
      ccmRestrictedWeilEvenPart a f := by
  simp [ccmRestrictedWeilEvenPart, map_add, map_smul, add_comm]

@[simp] theorem ccmArchimedeanFormReflection_oddPart
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormReflection a (ccmRestrictedWeilOddPart a f) =
      -ccmRestrictedWeilOddPart a f := by
  simp [ccmRestrictedWeilOddPart, map_sub, map_smul]
  module

theorem ccmRestrictedWeilEvenPart_add_oddPart
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilEvenPart a f + ccmRestrictedWeilOddPart a f = f := by
  unfold ccmRestrictedWeilEvenPart ccmRestrictedWeilOddPart
  module

theorem ccmRestrictedWeilEvenPart_sub_oddPart
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilEvenPart a f - ccmRestrictedWeilOddPart a f =
      ccmArchimedeanFormReflection a f := by
  unfold ccmRestrictedWeilEvenPart ccmRestrictedWeilOddPart
  module

/-- Parallelogram identity for the literal restricted-Weil quadratic on its complete form
domain. -/
theorem ccmRestrictedWeilSourceQuadratic_parallelogram
    (a : SuzukiPositiveAperture) (f g : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a (f + g) +
        ccmRestrictedWeilSourceQuadratic a (f - g) =
      2 * ccmRestrictedWeilSourceQuadratic a f +
        2 * ccmRestrictedWeilSourceQuadratic a g := by
  simp_rw [← ccmRestrictedWeilForm_self_re_eq_source]
  unfold ccmRestrictedWeilForm
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, Complex.add_re, Complex.sub_re]
  ring

/-- Exact energy splitting into the two reflection parities. -/
theorem ccmRestrictedWeilSourceQuadratic_evenOdd_split
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a f =
      ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilEvenPart a f) +
        ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilOddPart a f) := by
  have hpara := ccmRestrictedWeilSourceQuadratic_parallelogram a
    (ccmRestrictedWeilEvenPart a f) (ccmRestrictedWeilOddPart a f)
  rw [ccmRestrictedWeilEvenPart_add_oddPart,
    ccmRestrictedWeilEvenPart_sub_oddPart,
    ccmRestrictedWeilSourceQuadratic_reflection] at hpara
  linarith

theorem inner_ccmRestrictedWeilEvenPart_oddPart_physical
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    inner ℂ
        (ccmArchimedeanFormToAperture a (ccmRestrictedWeilEvenPart a f))
        (ccmArchimedeanFormToAperture a (ccmRestrictedWeilOddPart a f)) = 0 := by
  let e := ccmRestrictedWeilEvenPart a f
  let o := ccmRestrictedWeilOddPart a f
  let Je := ccmArchimedeanFormToAperture a e
  let Jo := ccmArchimedeanFormToAperture a o
  have he : ccmArchimedeanFormReflection a e = e := by
    exact ccmArchimedeanFormReflection_evenPart a f
  have ho : ccmArchimedeanFormReflection a o = -o := by
    exact ccmArchimedeanFormReflection_oddPart a f
  have hJev : l2Reflection (Je : SoninL2) = (Je : SoninL2) := by
    have h := ccmArchimedeanFormToAperture_reflection a e
    rw [he] at h
    exact h.symm
  have hJov : l2Reflection (Jo : SoninL2) = -(Jo : SoninL2) := by
    have h := ccmArchimedeanFormToAperture_reflection a o
    rw [ho, map_neg] at h
    exact h.symm
  change inner ℂ (Je : SoninL2) (Jo : SoninL2) = 0
  have hinv := l2ReflectionIsometry.inner_map_map (Je : SoninL2) (Jo : SoninL2)
  change inner ℂ (l2Reflection (Je : SoninL2))
      (l2Reflection (Jo : SoninL2)) =
    inner ℂ (Je : SoninL2) (Jo : SoninL2) at hinv
  rw [hJev, hJov, inner_neg_right] at hinv
  have hsum : inner ℂ (Je : SoninL2) (Jo : SoninL2) +
      inner ℂ (Je : SoninL2) (Jo : SoninL2) = 0 := by
    nth_rewrite 1 [← hinv]
    exact neg_add_cancel _
  have htwo : (2 : ℂ) * inner ℂ (Je : SoninL2) (Jo : SoninL2) = 0 := by
    calc
      _ = inner ℂ (Je : SoninL2) (Jo : SoninL2) +
          inner ℂ (Je : SoninL2) (Jo : SoninL2) := by ring
      _ = 0 := hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem norm_sq_ccmArchimedeanFormToAperture_evenOdd
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormToAperture a f‖ ^ 2 =
      ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilEvenPart a f)‖ ^ 2 +
        ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilOddPart a f)‖ ^ 2 := by
  let e := ccmRestrictedWeilEvenPart a f
  let o := ccmRestrictedWeilOddPart a f
  have hsum : f = e + o := (ccmRestrictedWeilEvenPart_add_oddPart a f).symm
  have horth : inner ℂ (ccmArchimedeanFormToAperture a e)
      (ccmArchimedeanFormToAperture a o) = 0 :=
    inner_ccmRestrictedWeilEvenPart_oddPart_physical a f
  change ‖ccmArchimedeanFormToAperture a f‖ ^ 2 =
    ‖ccmArchimedeanFormToAperture a e‖ ^ 2 +
      ‖ccmArchimedeanFormToAperture a o‖ ^ 2
  calc
    _ = ‖ccmArchimedeanFormToAperture a (e + o)‖ ^ 2 := by rw [← hsum]
    _ = ‖ccmArchimedeanFormToAperture a e +
          ccmArchimedeanFormToAperture a o‖ ^ 2 := by rw [map_add]
    _ = _ := by
      simpa [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
          (ccmArchimedeanFormToAperture a e)
          (ccmArchimedeanFormToAperture a o) horth)

/-- Each nonzero parity component of an attained exact ground state is itself an exact ground
state. -/
theorem ccmRestrictedWeil_ground_evenOdd_components
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a)
    (hground : ccmRestrictedWeilSourceQuadratic a f =
      ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a f‖ ^ 2) :
    ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilEvenPart a f) =
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilEvenPart a f)‖ ^ 2 ∧
      ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilOddPart a f) =
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilOddPart a f)‖ ^ 2 := by
  let e := ccmRestrictedWeilEvenPart a f
  let o := ccmRestrictedWeilOddPart a f
  have heFloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a e
  have hoFloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a o
  have henergy := ccmRestrictedWeilSourceQuadratic_evenOdd_split a f
  have hnorm := norm_sq_ccmArchimedeanFormToAperture_evenOdd a f
  dsimp only [e, o] at heFloor hoFloor ⊢
  have hbalance :
      (ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilEvenPart a f) -
          ccmRestrictedWeilGroundEnergy a *
            ‖ccmArchimedeanFormToAperture a
              (ccmRestrictedWeilEvenPart a f)‖ ^ 2) +
        (ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilOddPart a f) -
          ccmRestrictedWeilGroundEnergy a *
            ‖ccmArchimedeanFormToAperture a
              (ccmRestrictedWeilOddPart a f)‖ ^ 2) = 0 := by
    calc
      _ = ccmRestrictedWeilSourceQuadratic a f -
          ccmRestrictedWeilGroundEnergy a *
            ‖ccmArchimedeanFormToAperture a f‖ ^ 2 := by
              rw [henergy, hnorm]
              ring
      _ = 0 := by rw [hground]; ring
  constructor <;> linarith

/-- **Exact Route O parity reduction.** At every aperture, the literal restricted-Weil ground
has a nonzero complete-form representative of pure reflection parity. No simplicity or RH
hypothesis is used. -/
theorem exists_ccmRestrictedWeil_pureParity_groundFormState
    (a : SuzukiPositiveAperture) :
    ∃ f : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a f ≠ 0 ∧
      (ccmArchimedeanFormReflection a f = f ∨
        ccmArchimedeanFormReflection a f = -f) ∧
      ccmRestrictedWeilSourceQuadratic a f =
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a f‖ ^ 2 := by
  obtain ⟨u, hu, hground⟩ := ccmRestrictedWeilSource_exists_groundFormState a
  have hcomponents := ccmRestrictedWeil_ground_evenOdd_components a u hground
  let e := ccmRestrictedWeilEvenPart a u
  let o := ccmRestrictedWeilOddPart a u
  by_cases he : ccmArchimedeanFormToAperture a e = 0
  · refine ⟨o, ?_, Or.inr ?_, hcomponents.2⟩
    · intro ho
      apply hu
      rw [← ccmRestrictedWeilEvenPart_add_oddPart a u]
      rw [map_add, show ccmArchimedeanFormToAperture a e = 0 from he, ho, add_zero]
    · exact ccmArchimedeanFormReflection_oddPart a u
  · exact ⟨e, he, Or.inl (ccmArchimedeanFormReflection_evenPart a u), hcomponents.1⟩

end RHTower
