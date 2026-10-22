/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael
-/
import GaloisForLFunctions.RHTower.L2MellinUnitary
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# CCM logarithmic aperture unitary

This file formalizes Connes--Consani--Moscovici (2025), Proposition 3.2(i), without replacing its
source objects by a finite or abstract proxy.  For bundled `λ > 1`, it constructs the literal
logarithmic isometry

`L²([0, 2 log λ], dx) ≃ₗᵢ[ℂ] L²([λ⁻¹, λ], d*u)`,

where `d*u` is multiplicative Haar measure.  It proves the a.e. source formula
`κ(f)(u) = f(log (λu))`, exact sharp-support transport, and the induced equivalence of the two
closed-interval `C∞` spaces.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RHTower

/-- Source aperture parameter, bundling the published condition `λ > 1`. -/
abbrev CCMApertureParameter := { x : ℝ // 1 < x }

namespace CCMApertureParameter

theorem pos (lam : CCMApertureParameter) : 0 < (lam : ℝ) := lt_trans zero_lt_one lam.property
theorem log_pos (lam : CCMApertureParameter) : 0 < Real.log (lam : ℝ) := Real.log_pos lam.property

end CCMApertureParameter

def ccmLogLength (lam : CCMApertureParameter) : ℝ := 2 * Real.log (lam : ℝ)

def ccmAdditiveAperture (lam : CCMApertureParameter) : Set ℝ :=
  Icc 0 (ccmLogLength lam)

def ccmMultiplicativeAperture (lam : CCMApertureParameter) : Set MellinL2.PosReal :=
  Icc ⟨(lam : ℝ)⁻¹, inv_pos.mpr lam.pos⟩ ⟨(lam : ℝ), lam.pos⟩

theorem measurableSet_ccmMultiplicativeAperture (lam : CCMApertureParameter) :
    MeasurableSet (ccmMultiplicativeAperture lam) := measurableSet_Icc

theorem exp_mem_ccmMultiplicativeAperture_iff
    (lam : CCMApertureParameter) (t : ℝ) :
    MellinL2.expMeasurableEquiv t ∈ ccmMultiplicativeAperture lam ↔
      t + Real.log (lam : ℝ) ∈ ccmAdditiveAperture lam := by
  rw [ccmMultiplicativeAperture, ccmAdditiveAperture, mem_Icc, mem_Icc]
  change (lam : ℝ)⁻¹ ≤ Real.exp t ∧ Real.exp t ≤ (lam : ℝ) ↔
    0 ≤ t + Real.log (lam : ℝ) ∧ t + Real.log (lam : ℝ) ≤ 2 * Real.log (lam : ℝ)
  have hval : (lam : ℝ) = Real.exp (Real.log (lam : ℝ)) :=
    (Real.exp_log lam.pos).symm
  have hinv : (lam : ℝ)⁻¹ = Real.exp (-Real.log (lam : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log lam.pos]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hloExp : Real.exp (-Real.log (lam : ℝ)) ≤ Real.exp t := by
      rw [← hinv]
      exact hlo
    have hhiExp : Real.exp t ≤ Real.exp (Real.log (lam : ℝ)) := by
      rw [← hval]
      exact hhi
    constructor
    · have := Real.exp_le_exp.mp hloExp
      linarith
    · have := Real.exp_le_exp.mp hhiExp
      linarith
  · rintro ⟨hlo, hhi⟩
    have hloLog : -Real.log (lam : ℝ) ≤ t := by linarith
    have hhiLog : t ≤ Real.log (lam : ℝ) := by linarith
    constructor
    · rw [hinv]
      exact Real.exp_le_exp.mpr hloLog
    · rw [hval]
      exact Real.exp_le_exp.mpr hhiLog

def ccmLogApertureUnitary (lam : CCMApertureParameter) :
    SoninL2 ≃ₗᵢ[ℂ] Lp ℂ 2 MellinL2.multiplicativeHaar :=
  (MellinL2.additiveTranslationUnitary (Real.log (lam : ℝ))).trans
    MellinL2.expPullbackUnitary.symm

theorem expPullback_ccmLogApertureUnitary
    (lam : CCMApertureParameter) (f : SoninL2) :
    MellinL2.expPullbackUnitary (ccmLogApertureUnitary lam f) =
      MellinL2.additiveTranslationUnitary (Real.log (lam : ℝ)) f := by
  simp [ccmLogApertureUnitary]

theorem ccmLogApertureUnitary_ae
    (lam : CCMApertureParameter) (f : SoninL2) :
    (fun t : ℝ => ccmLogApertureUnitary lam f (MellinL2.expMeasurableEquiv t))
      =ᵐ[volume]
    (fun t : ℝ => f (t + Real.log (lam : ℝ))) := by
  have hpull := Lp.coeFn_compMeasurePreserving
    (ccmLogApertureUnitary lam f) MellinL2.exp_measurePreserving
  have htrans := Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving (Real.log (lam : ℝ)))
  filter_upwards [hpull, htrans] with t hp ht
  calc
    ccmLogApertureUnitary lam f (MellinL2.expMeasurableEquiv t) =
        MellinL2.expPullbackUnitary (ccmLogApertureUnitary lam f) t := hp.symm
    _ = MellinL2.additiveTranslationUnitary (Real.log (lam : ℝ)) f t :=
      congrArg (fun g : SoninL2 => g t) (expPullback_ccmLogApertureUnitary lam f)
    _ = f (t + Real.log (lam : ℝ)) := by
      change Lp.compMeasurePreserving
        (MellinL2.realTranslationEquiv (Real.log (lam : ℝ)))
        (MellinL2.realTranslation_measurePreserving (Real.log (lam : ℝ))) f t = _
      simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using ht

/-- Sharp cutoff to the source interval `[0, 2 log λ]`. -/
abbrev ccmAdditiveApertureCutoff (lam : CCMApertureParameter) :
    SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (ccmAdditiveAperture lam) measurableSet_Icc

/-- Sharp cutoff to the multiplicative aperture `[λ⁻¹, λ]`. -/
def ccmMultiplicativeApertureCutoff (lam : CCMApertureParameter) :
    Lp ℂ 2 MellinL2.multiplicativeHaar →L[ℂ]
      Lp ℂ 2 MellinL2.multiplicativeHaar :=
  lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) MellinL2.multiplicativeHaar 2
    (ccmMultiplicativeAperture lam) (measurableSet_ccmMultiplicativeAperture lam)

theorem ccmMultiplicativeApertureCutoff_ae (lam : CCMApertureParameter)
    (f : Lp ℂ 2 MellinL2.multiplicativeHaar) :
    ccmMultiplicativeApertureCutoff lam f =ᵐ[MellinL2.multiplicativeHaar]
      (ccmMultiplicativeAperture lam).indicator fun u => f u :=
  lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ) MellinL2.multiplicativeHaar 2
    (ccmMultiplicativeAperture lam) (measurableSet_ccmMultiplicativeAperture lam) f

theorem ccmMultiplicativeApertureCutoff_idempotent (lam : CCMApertureParameter) :
    IsIdempotentElem (ccmMultiplicativeApertureCutoff lam) := by
  rw [isIdempotentElem_iff]
  ext f
  simp only [mul_apply_eq_comp]
  filter_upwards [ccmMultiplicativeApertureCutoff_ae lam
      (ccmMultiplicativeApertureCutoff lam f),
    ccmMultiplicativeApertureCutoff_ae lam f] with u h1 h2
  rw [h1]
  by_cases hu : u ∈ ccmMultiplicativeAperture lam
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]
    simpa [hu] using h2.symm

/-- Exact support transport in CCM Proposition 3.2(i): logarithmic translation conjugates the
two sharp aperture projections. -/
theorem ccmLogApertureUnitary_cutoff_intertwining
    (lam : CCMApertureParameter) (f : SoninL2) :
    ccmMultiplicativeApertureCutoff lam (ccmLogApertureUnitary lam f) =
      ccmLogApertureUnitary lam (ccmAdditiveApertureCutoff lam f) := by
  classical
  apply MellinL2.expPullbackUnitary.injective
  apply Lp.ext
  have hpull := Lp.coeFn_compMeasurePreserving
    (ccmMultiplicativeApertureCutoff lam (ccmLogApertureUnitary lam f))
    MellinL2.exp_measurePreserving
  have hpullRight := Lp.coeFn_compMeasurePreserving
    (ccmLogApertureUnitary lam (ccmAdditiveApertureCutoff lam f))
    MellinL2.exp_measurePreserving
  have htarget := (ccmMultiplicativeApertureCutoff_ae lam
    (ccmLogApertureUnitary lam f)).comp_tendsto
      MellinL2.exp_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hunit := ccmLogApertureUnitary_ae lam f
  have hunitCut := ccmLogApertureUnitary_ae lam (ccmAdditiveApertureCutoff lam f)
  have hsource := (indicatorCutoff_ae (ccmAdditiveAperture lam) measurableSet_Icc f).comp_tendsto
    (MellinL2.realTranslation_measurePreserving (Real.log (lam : ℝ))).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hpull, hpullRight, htarget, hunit, hunitCut, hsource]
      with t hp hpRight ht hu huCut hs
  change Lp.compMeasurePreserving MellinL2.expMeasurableEquiv
      MellinL2.exp_measurePreserving
      (ccmMultiplicativeApertureCutoff lam (ccmLogApertureUnitary lam f)) t =
    Lp.compMeasurePreserving MellinL2.expMeasurableEquiv
      MellinL2.exp_measurePreserving
      (ccmLogApertureUnitary lam (ccmAdditiveApertureCutoff lam f)) t
  rw [hp, hpRight, ht]
  simp only [Function.comp_apply]
  rw [huCut]
  have hsAt : ccmAdditiveApertureCutoff lam f (t + Real.log (lam : ℝ)) =
      (ccmAdditiveAperture lam).indicator (fun x => f x)
        (t + Real.log (lam : ℝ)) := by
    simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hs
  rw [hsAt]
  change (ccmMultiplicativeAperture lam).indicator
      (fun u => ccmLogApertureUnitary lam f u) (MellinL2.expMeasurableEquiv t) =
    (ccmAdditiveAperture lam).indicator (fun x => f x)
      (t + Real.log (lam : ℝ))
  have hmem := exp_mem_ccmMultiplicativeAperture_iff lam t
  by_cases htmem : MellinL2.expMeasurableEquiv t ∈ ccmMultiplicativeAperture lam
  · have hsmem := hmem.mp htmem
    simp [htmem, hsmem, hu]
  · have hsnmem : t + Real.log (lam : ℝ) ∉ ccmAdditiveAperture lam :=
      fun hs => htmem (hmem.mpr hs)
    simp [htmem, hsnmem]

/-- Zero-extended model of `L²([0, 2 log λ], dx)`. -/
def ccmAdditiveApertureSubspace (lam : CCMApertureParameter) : Submodule ℂ SoninL2 :=
  LinearMap.range (ccmAdditiveApertureCutoff lam).toLinearMap

/-- Zero-extended model of `L²([λ⁻¹, λ], d*u)`. -/
def ccmMultiplicativeApertureSubspace (lam : CCMApertureParameter) :
    Submodule ℂ (Lp ℂ 2 MellinL2.multiplicativeHaar) :=
  LinearMap.range (ccmMultiplicativeApertureCutoff lam).toLinearMap

private theorem ccmLogApertureUnitary_maps_additive_to_multiplicative
    (lam : CCMApertureParameter) (f : ccmAdditiveApertureSubspace lam) :
    ccmLogApertureUnitary lam (f : SoninL2) ∈ ccmMultiplicativeApertureSubspace lam := by
  rcases f.property with ⟨g, hg⟩
  refine ⟨ccmLogApertureUnitary lam g, ?_⟩
  change ccmMultiplicativeApertureCutoff lam (ccmLogApertureUnitary lam g) =
    ccmLogApertureUnitary lam (f : SoninL2)
  rw [ccmLogApertureUnitary_cutoff_intertwining]
  exact congrArg (ccmLogApertureUnitary lam) hg

private theorem ccmLogApertureUnitary_symm_maps_multiplicative_to_additive
    (lam : CCMApertureParameter) (f : ccmMultiplicativeApertureSubspace lam) :
    (ccmLogApertureUnitary lam).symm
        (f : Lp ℂ 2 MellinL2.multiplicativeHaar) ∈ ccmAdditiveApertureSubspace lam := by
  rcases f.property with ⟨g, hg⟩
  refine ⟨(ccmLogApertureUnitary lam).symm g, ?_⟩
  apply (ccmLogApertureUnitary lam).injective
  calc
    ccmLogApertureUnitary lam
        (ccmAdditiveApertureCutoff lam ((ccmLogApertureUnitary lam).symm g)) =
        ccmMultiplicativeApertureCutoff lam
          (ccmLogApertureUnitary lam ((ccmLogApertureUnitary lam).symm g)) :=
      (ccmLogApertureUnitary_cutoff_intertwining lam
        ((ccmLogApertureUnitary lam).symm g)).symm
    _ = ccmMultiplicativeApertureCutoff lam g := by
      rw [(ccmLogApertureUnitary lam).apply_symm_apply]
    _ = (f : Lp ℂ 2 MellinL2.multiplicativeHaar) := hg
    _ = ccmLogApertureUnitary lam
        ((ccmLogApertureUnitary lam).symm
          (f : Lp ℂ 2 MellinL2.multiplicativeHaar)) :=
      ((ccmLogApertureUnitary lam).apply_symm_apply
        (f : Lp ℂ 2 MellinL2.multiplicativeHaar)).symm

/-- CCM Proposition 3.2(i), represented on literal zero-extended interval subspaces. -/
def ccmLogApertureSubspaceIsometry (lam : CCMApertureParameter) :
    ccmAdditiveApertureSubspace lam ≃ₗᵢ[ℂ] ccmMultiplicativeApertureSubspace lam where
  toFun f := ⟨ccmLogApertureUnitary lam (f : SoninL2),
    ccmLogApertureUnitary_maps_additive_to_multiplicative lam f⟩
  invFun f := ⟨(ccmLogApertureUnitary lam).symm
      (f : Lp ℂ 2 MellinL2.multiplicativeHaar),
    ccmLogApertureUnitary_symm_maps_multiplicative_to_additive lam f⟩
  map_add' f g := by
    apply Subtype.ext
    exact (ccmLogApertureUnitary lam).map_add (f : SoninL2) (g : SoninL2)
  map_smul' c f := by
    apply Subtype.ext
    exact (ccmLogApertureUnitary lam).map_smul c (f : SoninL2)
  left_inv f := by
    apply Subtype.ext
    exact (ccmLogApertureUnitary lam).symm_apply_apply (f : SoninL2)
  right_inv f := by
    apply Subtype.ext
    exact (ccmLogApertureUnitary lam).apply_symm_apply
      (f : Lp ℂ 2 MellinL2.multiplicativeHaar)
  norm_map' f := (ccmLogApertureUnitary lam).norm_map (f : SoninL2)

@[simp] theorem ccmLogApertureSubspaceIsometry_coe
    (lam : CCMApertureParameter) (f : ccmAdditiveApertureSubspace lam) :
    ((ccmLogApertureSubspaceIsometry lam f : ccmMultiplicativeApertureSubspace lam) :
      Lp ℂ 2 MellinL2.multiplicativeHaar) =
      ccmLogApertureUnitary lam (f : SoninL2) := rfl

/-! ### Literal restricted-measure `L²` spaces -/

theorem ccmLpSetCutoff_idempotent {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : Set X) (hs : MeasurableSet s) :
    IsIdempotentElem
      (lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs) := by
  classical
  rw [isIdempotentElem_iff]
  ext f
  simp only [mul_apply_eq_comp]
  filter_upwards [lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ) ν 2 s hs
      (lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f),
    lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ) ν 2 s hs f] with x h1 h2
  rw [h1]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    simpa [hx] using h2.symm

theorem ccmLpRestrict_extendByZero {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℂ 2 (ν.restrict s)) :
    LpToLpRestrictCLM X ℂ ℂ ν 2 s
        (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f) = f := by
  apply Lp.ext
  have hext := lpExtendByZeroCLM_coeFn (F := ℂ) (𝕜 := ℂ) ν 2 s hs f
  have hextRestrict :
      lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f =ᵐ[ν.restrict s]
        fun x => f x := by
    change ∀ᵐ x ∂ν.restrict s,
      lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f x = f x
    rw [ae_restrict_iff' hs]
    filter_upwards [hext] with x hx hxs
    simpa [hxs] using hx
  filter_upwards [
    LpToLpRestrictCLM_coeFn (μ := ν) (p := (2 : ENNReal)) ℂ s
      (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f),
    hextRestrict] with x hres hextx
  exact hres.trans hextx

theorem ccmLpSetCutoff_extendByZero {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℂ 2 (ν.restrict s)) :
    lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs
        (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f) =
      lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f := by
  change lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs
      (LpToLpRestrictCLM X ℂ ℂ ν 2 s
        (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f)) = _
  rw [ccmLpRestrict_extendByZero]

/-- Extension by zero identifies a literal restricted-measure `L²` space isometrically with the
range of its sharp cutoff. -/
def ccmLpRestrictRangeIsometry {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : Set X) (hs : MeasurableSet s) :
    Lp ℂ 2 (ν.restrict s) ≃ₗᵢ[ℂ]
      LinearMap.range (lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs).toLinearMap where
  toFun f := ⟨lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f,
    ⟨lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs f,
      ccmLpSetCutoff_extendByZero ν s hs f⟩⟩
  invFun f := LpToLpRestrictCLM X ℂ ℂ ν 2 s (f : Lp ℂ 2 ν)
  map_add' f g := by
    apply Subtype.ext
    exact (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs).map_add f g
  map_smul' c f := by
    apply Subtype.ext
    exact (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs).map_smul c f
  left_inv f := ccmLpRestrict_extendByZero ν s hs f
  right_inv f := by
    apply Subtype.ext
    have hp : IsIdempotentElem
        (lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs).toLinearMap :=
      ContinuousLinearMap.IsIdempotentElem.toLinearMap
        (ccmLpSetCutoff_idempotent ν s hs)
    have hfixed := (LinearMap.IsIdempotentElem.mem_range_iff hp).mp f.property
    change lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) ν 2 s hs
      (f : Lp ℂ 2 ν) = (f : Lp ℂ 2 ν)
    exact hfixed
  norm_map' f := norm_lpExtendByZero ν 2 s hs f

/-- Literal source Hilbert space `L²([0, 2 log λ], dx)`, using restricted Lebesgue measure. -/
abbrev CCMAdditiveIntervalL2 (lam : CCMApertureParameter) :=
  Lp ℂ 2 ((volume : Measure ℝ).restrict (ccmAdditiveAperture lam))

/-- Literal target Hilbert space `L²([λ⁻¹, λ], d*u)`, using restricted multiplicative Haar. -/
abbrev CCMMultiplicativeIntervalL2 (lam : CCMApertureParameter) :=
  Lp ℂ 2 (MellinL2.multiplicativeHaar.restrict (ccmMultiplicativeAperture lam))

def ccmAdditiveIntervalExtension (lam : CCMApertureParameter) :
    CCMAdditiveIntervalL2 lam ≃ₗᵢ[ℂ] ccmAdditiveApertureSubspace lam :=
  ccmLpRestrictRangeIsometry (volume : Measure ℝ) (ccmAdditiveAperture lam)
    measurableSet_Icc

def ccmMultiplicativeIntervalExtension (lam : CCMApertureParameter) :
    CCMMultiplicativeIntervalL2 lam ≃ₗᵢ[ℂ] ccmMultiplicativeApertureSubspace lam :=
  ccmLpRestrictRangeIsometry MellinL2.multiplicativeHaar
    (ccmMultiplicativeAperture lam) (measurableSet_ccmMultiplicativeAperture lam)

/-- CCM Proposition 3.2(i), literally as an onto isometry
`L²([0,L],dx) ≃ L²([λ⁻¹,λ],d*u)` with `L = 2 log λ`. -/
def ccmLogApertureIsometry (lam : CCMApertureParameter) :
    CCMAdditiveIntervalL2 lam ≃ₗᵢ[ℂ] CCMMultiplicativeIntervalL2 lam :=
  (ccmAdditiveIntervalExtension lam).trans
    ((ccmLogApertureSubspaceIsometry lam).trans
      (ccmMultiplicativeIntervalExtension lam).symm)

theorem ccmLogApertureIsometry_extension
    (lam : CCMApertureParameter) (f : CCMAdditiveIntervalL2 lam) :
    ccmMultiplicativeIntervalExtension lam (ccmLogApertureIsometry lam f) =
      ccmLogApertureSubspaceIsometry lam (ccmAdditiveIntervalExtension lam f) := by
  simp [ccmLogApertureIsometry]

theorem ccmLogApertureIsometry_ae
    (lam : CCMApertureParameter) (f : CCMAdditiveIntervalL2 lam) :
    (fun t : ℝ =>
      ((ccmMultiplicativeIntervalExtension lam (ccmLogApertureIsometry lam f) :
        ccmMultiplicativeApertureSubspace lam) :
          Lp ℂ 2 MellinL2.multiplicativeHaar) (MellinL2.expMeasurableEquiv t)) =ᵐ[volume]
    (fun t : ℝ =>
      ((ccmAdditiveIntervalExtension lam f : ccmAdditiveApertureSubspace lam) : SoninL2)
        (t + Real.log (lam : ℝ))) := by
  rw [ccmLogApertureIsometry_extension]
  exact ccmLogApertureUnitary_ae lam
    ((ccmAdditiveIntervalExtension lam f : ccmAdditiveApertureSubspace lam) : SoninL2)

/-! ### Smooth closed-interval transport -/

def ccmMultiplicativeRealAperture (lam : CCMApertureParameter) : Set ℝ :=
  Icc (lam : ℝ)⁻¹ (lam : ℝ)

def ccmKappaCoordinate (lam : CCMApertureParameter) (u : ℝ) : ℝ :=
  Real.log ((lam : ℝ) * u)

def ccmKappaInverseCoordinate (lam : CCMApertureParameter) (x : ℝ) : ℝ :=
  Real.exp x / (lam : ℝ)

theorem ccmKappaCoordinate_mapsTo (lam : CCMApertureParameter) :
    MapsTo (ccmKappaCoordinate lam) (ccmMultiplicativeRealAperture lam)
      (ccmAdditiveAperture lam) := by
  intro u hu
  rw [ccmMultiplicativeRealAperture, mem_Icc] at hu
  rw [ccmAdditiveAperture, mem_Icc]
  have huPos : 0 < u := lt_of_lt_of_le (inv_pos.mpr lam.pos) hu.1
  have hlamne : (lam : ℝ) ≠ 0 := lam.pos.ne'
  have hmulOne : 1 ≤ (lam : ℝ) * u := by
    calc
      1 = (lam : ℝ) * (lam : ℝ)⁻¹ := (mul_inv_cancel₀ hlamne).symm
      _ ≤ (lam : ℝ) * u := mul_le_mul_of_nonneg_left hu.1 lam.pos.le
  constructor
  · exact Real.log_nonneg hmulOne
  · rw [ccmKappaCoordinate, ccmLogLength,
      Real.log_mul hlamne huPos.ne']
    have hlog := Real.log_le_log huPos hu.2
    linarith

theorem ccmKappaInverseCoordinate_mapsTo (lam : CCMApertureParameter) :
    MapsTo (ccmKappaInverseCoordinate lam) (ccmAdditiveAperture lam)
      (ccmMultiplicativeRealAperture lam) := by
  intro x hx
  rw [ccmAdditiveAperture, mem_Icc] at hx
  rw [ccmMultiplicativeRealAperture, mem_Icc]
  have hexpOne : 1 ≤ Real.exp x := by
    simpa using Real.exp_le_exp.mpr hx.1
  have hexpTop : Real.exp x ≤ (lam : ℝ) * (lam : ℝ) := by
    have h := Real.exp_le_exp.mpr hx.2
    rw [ccmLogLength, show 2 * Real.log (lam : ℝ) =
      Real.log (lam : ℝ) + Real.log (lam : ℝ) by ring,
      Real.exp_add, Real.exp_log lam.pos] at h
    exact h
  constructor
  · rw [ccmKappaInverseCoordinate, show (lam : ℝ)⁻¹ = 1 / (lam : ℝ) by simp]
    exact (div_le_div_iff_of_pos_right lam.pos).2 hexpOne
  · rw [ccmKappaInverseCoordinate]
    exact (div_le_iff₀ lam.pos).2 hexpTop

theorem ccmKappaCoordinate_inverse (lam : CCMApertureParameter)
    (x : ℝ) :
    ccmKappaCoordinate lam (ccmKappaInverseCoordinate lam x) = x := by
  rw [ccmKappaCoordinate, ccmKappaInverseCoordinate]
  have hlamne : (lam : ℝ) ≠ 0 := lam.pos.ne'
  have hmul : (lam : ℝ) * (Real.exp x / (lam : ℝ)) = Real.exp x := by
    field_simp
  rw [hmul, Real.log_exp]

theorem ccmKappaInverseCoordinate_coordinate (lam : CCMApertureParameter)
    (u : ccmMultiplicativeRealAperture lam) :
    ccmKappaInverseCoordinate lam (ccmKappaCoordinate lam u) = (u : ℝ) := by
  have hu := u.property
  change (lam : ℝ)⁻¹ ≤ (u : ℝ) ∧ (u : ℝ) ≤ (lam : ℝ) at hu
  have huPos : 0 < (u : ℝ) := lt_of_lt_of_le (inv_pos.mpr lam.pos) hu.1
  rw [ccmKappaInverseCoordinate, ccmKappaCoordinate,
    Real.exp_log (mul_pos lam.pos huPos)]
  field_simp
  exact div_self lam.pos.ne'

theorem ccmKappaCoordinate_contDiffOn (lam : CCMApertureParameter) :
    ContDiffOn ℝ ⊤ (ccmKappaCoordinate lam) (ccmMultiplicativeRealAperture lam) := by
  apply (contDiff_const.mul contDiff_id).contDiffOn.log
  intro u hu
  rw [ccmMultiplicativeRealAperture, mem_Icc] at hu
  exact mul_ne_zero lam.pos.ne'
    (lt_of_lt_of_le (inv_pos.mpr lam.pos) hu.1).ne'

theorem ccmKappaInverseCoordinate_contDiff (lam : CCMApertureParameter) :
    ContDiff ℝ ⊤ (ccmKappaInverseCoordinate lam) := by
  exact Real.contDiff_exp.div_const (lam : ℝ)

/-- `C∞(s)` on a closed real interval, represented intrinsically as functions on `s` admitting a
smooth ambient extension along `s`. -/
def CCMSmoothOn (s : Set ℝ) :=
  { f : s → ℂ // ∃ F : ℝ → ℂ, ContDiffOn ℝ ⊤ F s ∧ ∀ x : s, F x = f x }

instance (s : Set ℝ) : CoeFun (CCMSmoothOn s) (fun _ => s → ℂ) :=
  ⟨fun f => f.1⟩

def ccmSmoothKappa (lam : CCMApertureParameter) :
    CCMSmoothOn (ccmAdditiveAperture lam) →
      CCMSmoothOn (ccmMultiplicativeRealAperture lam) := fun f => by
  refine ⟨fun u => f ⟨ccmKappaCoordinate lam u, ccmKappaCoordinate_mapsTo lam u.property⟩, ?_⟩
  rcases f.property with ⟨F, hF, hFeq⟩
  refine ⟨fun u => F (ccmKappaCoordinate lam u),
    hF.comp (ccmKappaCoordinate_contDiffOn lam) (ccmKappaCoordinate_mapsTo lam), ?_⟩
  intro u
  exact hFeq ⟨ccmKappaCoordinate lam u, ccmKappaCoordinate_mapsTo lam u.property⟩

def ccmSmoothKappaInverse (lam : CCMApertureParameter) :
    CCMSmoothOn (ccmMultiplicativeRealAperture lam) →
      CCMSmoothOn (ccmAdditiveAperture lam) := fun f => by
  refine ⟨fun x => f ⟨ccmKappaInverseCoordinate lam x,
    ccmKappaInverseCoordinate_mapsTo lam x.property⟩, ?_⟩
  rcases f.property with ⟨F, hF, hFeq⟩
  refine ⟨fun x => F (ccmKappaInverseCoordinate lam x),
    hF.comp (ccmKappaInverseCoordinate_contDiff lam).contDiffOn
      (ccmKappaInverseCoordinate_mapsTo lam), ?_⟩
  intro x
  exact hFeq ⟨ccmKappaInverseCoordinate lam x,
    ccmKappaInverseCoordinate_mapsTo lam x.property⟩

/-- CCM Proposition 3.2(i), smooth clause: pullback by `u ↦ log(λu)` is an equivalence between
the two literal closed-interval `C∞` spaces. -/
def ccmSmoothKappaEquiv (lam : CCMApertureParameter) :
    CCMSmoothOn (ccmAdditiveAperture lam) ≃
      CCMSmoothOn (ccmMultiplicativeRealAperture lam) where
  toFun := ccmSmoothKappa lam
  invFun := ccmSmoothKappaInverse lam
  left_inv f := by
    apply Subtype.ext
    funext x
    change f ⟨ccmKappaCoordinate lam (ccmKappaInverseCoordinate lam x), _⟩ = f x
    have hx : (⟨ccmKappaCoordinate lam (ccmKappaInverseCoordinate lam x),
        ccmKappaCoordinate_mapsTo lam
          (ccmKappaInverseCoordinate_mapsTo lam x.property)⟩ :
        ccmAdditiveAperture lam) = x :=
      Subtype.ext (ccmKappaCoordinate_inverse lam x)
    exact congrArg (fun y : ccmAdditiveAperture lam => f y) hx
  right_inv f := by
    apply Subtype.ext
    funext u
    change f ⟨ccmKappaInverseCoordinate lam (ccmKappaCoordinate lam u), _⟩ = f u
    have hu : (⟨ccmKappaInverseCoordinate lam (ccmKappaCoordinate lam u),
        ccmKappaInverseCoordinate_mapsTo lam
          (ccmKappaCoordinate_mapsTo lam u.property)⟩ :
        ccmMultiplicativeRealAperture lam) = u :=
      Subtype.ext (ccmKappaInverseCoordinate_coordinate lam u)
    exact congrArg (fun v : ccmMultiplicativeRealAperture lam => f v) hu

end RHTower
