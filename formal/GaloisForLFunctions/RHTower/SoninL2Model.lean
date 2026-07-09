/-
Concrete fixed-cutoff Sonin infrastructure on complex L²(ℝ).

This file contains no analytic hypotheses. It constructs the physical indicator cutoff and proves
that it is an orthogonal projection, its Fourier conjugate, the even carrier, normalized dilation
unitaries and their adjoints, and an explicit orthonormal sequence of symmetric shell indicators.
The shell vectors obey the exact inward/outward support identities for U_p + U_p*. The final section
identifies restricted-measure L² with the subtype-interval L² used by the finite-rectangle Fourier
compactness theorem, including explicit restriction and zero-extension maps.
-/
import GaloisForLFunctions.RHTower.FiniteTimeBandFourierCompact
import GaloisForLFunctions.RHTower.L2FourierReflection
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

namespace RHTower

abbrev SoninL2 := Lp (α := ℝ) ℂ 2

/-! ### Physical and Fourier cutoffs -/

def indicatorCutoff (s : Set ℝ) (hs : MeasurableSet s) : SoninL2 →L[ℂ] SoninL2 :=
  lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2 s hs

theorem indicatorCutoff_ae (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    indicatorCutoff s hs f =ᵐ[volume] s.indicator fun x => f x :=
  lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2 s hs f

theorem indicatorCutoff_idempotent (s : Set ℝ) (hs : MeasurableSet s) :
    IsIdempotentElem (indicatorCutoff s hs) := by
  rw [isIdempotentElem_iff]
  ext f
  ext1
  filter_upwards [indicatorCutoff_ae s hs (indicatorCutoff s hs f),
    indicatorCutoff_ae s hs f] with x h1 h2
  rw [h1, h2]
  simp

theorem indicatorCutoff_symmetric (s : Set ℝ) (hs : MeasurableSet s) :
    (indicatorCutoff s hs).toLinearMap.IsSymmetric := by
  intro f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorCutoff_ae s hs f, indicatorCutoff_ae s hs g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s <;> simp [hx]

theorem indicatorCutoff_isStarProjection (s : Set ℝ) (hs : MeasurableSet s) :
    IsStarProjection (indicatorCutoff s hs) := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨(indicatorCutoff_idempotent s hs).toLinearMap,
    indicatorCutoff_symmetric s hs⟩

def physicalForbidden (s : Set ℝ) (hs : MeasurableSet s) : Submodule ℂ SoninL2 :=
  LinearMap.range (indicatorCutoff s hs).toLinearMap

instance physicalForbidden_hasOrthogonalProjection (s : Set ℝ) (hs : MeasurableSet s) :
    (physicalForbidden s hs).HasOrthogonalProjection :=
  (indicatorCutoff_isStarProjection s hs).isSymmetricProjection.hasOrthogonalProjection_range

theorem indicatorCutoff_eq_physicalForbidden_starProjection
    (s : Set ℝ) (hs : MeasurableSet s) :
    indicatorCutoff s hs = (physicalForbidden s hs).starProjection :=
  (ContinuousLinearMap.isStarProjection_iff_eq_starProjection_range.mp
    (indicatorCutoff_isStarProjection s hs)).2


def fourierUnitary : SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

def fourierCutoff (s : Set ℝ) (hs : MeasurableSet s) : SoninL2 →L[ℂ] SoninL2 :=
  fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    indicatorCutoff s hs ∘L
    fourierUnitary.toLinearIsometry.toContinuousLinearMap

@[simp] theorem fourierCutoff_apply (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    fourierCutoff s hs f = fourierUnitary.symm (indicatorCutoff s hs (fourierUnitary f)) := rfl

theorem fourierCutoff_idempotent (s : Set ℝ) (hs : MeasurableSet s) :
    IsIdempotentElem (fourierCutoff s hs) := by
  rw [isIdempotentElem_iff]
  ext f
  simp only [ContinuousLinearMap.mul_apply, fourierCutoff_apply,
    LinearIsometryEquiv.apply_symm_apply]
  have hP := indicatorCutoff_idempotent s hs
  rw [isIdempotentElem_iff] at hP
  exact congrArg fourierUnitary.symm (DFunLike.congr_fun (congrArg DFunLike.coe hP)
    (fourierUnitary f))

theorem fourierCutoff_symmetric (s : Set ℝ) (hs : MeasurableSet s) :
    (fourierCutoff s hs).toLinearMap.IsSymmetric := by
  intro f g
  rw [← fourierUnitary.inner_map_map]
  simp only [fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [← fourierUnitary.inner_map_map]
  simp only [fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply]
  exact indicatorCutoff_symmetric s hs (fourierUnitary f) (fourierUnitary g)

theorem fourierCutoff_isStarProjection (s : Set ℝ) (hs : MeasurableSet s) :
    IsStarProjection (fourierCutoff s hs) := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨(fourierCutoff_idempotent s hs).toLinearMap,
    fourierCutoff_symmetric s hs⟩

def fourierForbidden (s : Set ℝ) (hs : MeasurableSet s) : Submodule ℂ SoninL2 :=
  LinearMap.range (fourierCutoff s hs).toLinearMap

instance fourierForbidden_hasOrthogonalProjection (s : Set ℝ) (hs : MeasurableSet s) :
    (fourierForbidden s hs).HasOrthogonalProjection :=
  (fourierCutoff_isStarProjection s hs).isSymmetricProjection.hasOrthogonalProjection_range

theorem fourierCutoff_eq_fourierForbidden_starProjection
    (s : Set ℝ) (hs : MeasurableSet s) :
    fourierCutoff s hs = (fourierForbidden s hs).starProjection :=
  (ContinuousLinearMap.isStarProjection_iff_eq_starProjection_range.mp
    (fourierCutoff_isStarProjection s hs)).2

/-! ### Full-space finite time-band compactness -/

theorem fullToRestrictedTimeBandFourier_coeFn_sonin
    (a b c d : ℝ) (hab : a ≤ b) (f : SoninL2) :
    (fullToRestrictedTimeBandFourier a b c d hab f : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict (Set.Icc a b)]
      fun x => ∫ y : ℝ in Set.Icc c d,
        Complex.exp ((-(2 * Real.pi * x * y) : ℝ) * Complex.I) * f y := by
  filter_upwards [
    (evalBilinear (E := SoninL2)).coeFn_holder (r := (2 : ENNReal))
      (fullFourierFunctionalField a b c d hab)
      (Lp.const ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)) f),
    BoundedContinuousFunction.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure ℝ).restrict (Set.Icc a b))
      (fullFourierFunctionalBCF a b c d hab),
    Lp.coeFn_const (p := ∞) ((volume : Measure ℝ).restrict (Set.Icc a b)) f,
    ae_restrict_mem measurableSet_mem
  ] with x hholder hfield hconst hx
  rw [fullToRestrictedTimeBandFourier, kernelOperator, kernelOperatorMap_apply,
    hholder, fullFourierFunctionalField, hfield, hconst]
  change fullFourierFunctionalContinuous a b c d (Set.projIcc a b hab x) f = _
  rw [Set.projIcc_of_mem hab hx]
  exact fullFourierFunctionalContinuous_apply a b c d ⟨x, hx⟩ f

theorem fullTimeBandFourier_coeFn_sonin
    (a b c d : ℝ) (hab : a ≤ b) (f : SoninL2) :
    (fullTimeBandFourier a b c d hab f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Set.Icc a b).indicator (fun x => ∫ y : ℝ in Set.Icc c d,
        Complex.exp ((-(2 * Real.pi * x * y) : ℝ) * Complex.I) * f y) x := by
  have hinner : ∀ᵐ x ∂volume, x ∈ Set.Icc a b →
      fullToRestrictedTimeBandFourier a b c d hab f x =
        ∫ y : ℝ in Set.Icc c d,
          Complex.exp ((-(2 * Real.pi * x * y) : ℝ) * Complex.I) * f y :=
    (ae_restrict_iff' measurableSet_Icc).mp
      (fullToRestrictedTimeBandFourier_coeFn_sonin a b c d hab f)
  filter_upwards [
    lpExtendByZeroCLM_coeFn (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Set.Icc a b) measurableSet_Icc
      (fullToRestrictedTimeBandFourier a b c d hab f),
    hinner
  ] with x hext hinnerx
  rw [fullTimeBandFourier, ContinuousLinearMap.comp_apply, hext]
  by_cases hx : x ∈ Set.Icc a b
  · simp [hx, hinnerx hx]
  · simp [hx]

theorem integrable_indicatorCutoff_Icc (c d : ℝ) (f : SoninL2) :
    Integrable (indicatorCutoff (Set.Icc c d) measurableSet_Icc f : ℝ → ℂ) := by
  have hindicator : Integrable ((Set.Icc c d).indicator fun x : ℝ => f x) :=
    (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim
      (by finiteness)).integrable_indicator measurableSet_Icc
  exact hindicator.congr (indicatorCutoff_ae (Set.Icc c d) measurableSet_Icc f).symm

theorem l1Fourier_indicatorCutoff_Icc_eq_setIntegral
    (c d : ℝ) (f : SoninL2) (x : ℝ) :
    let g := indicatorCutoff (Set.Icc c d) measurableSet_Icc f
    Lp.fourierTransform
        ((memLp_one_iff_integrable.mpr (integrable_indicatorCutoff_Icc c d f)).toLp g) x =
      ∫ y : ℝ in Set.Icc c d,
        Complex.exp ((-(2 * Real.pi * x * y) : ℝ) * Complex.I) * f y := by
  dsimp only
  rw [Lp.fourierTransform_apply, Real.fourier_eq', ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [indicatorCutoff_ae (Set.Icc c d) measurableSet_Icc f] with y hy
  rw [hy]
  by_cases hys : y ∈ Set.Icc c d
  · simp [hys, smul_eq_mul, Real.inner_apply, mul_comm]
  · simp [hys]

def cutoffFourierCutoff (a b c d : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Set.Icc a b) measurableSet_Icc ∘L
    fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    indicatorCutoff (Set.Icc c d) measurableSet_Icc

theorem fullTimeBandFourier_eq_cutoffFourierCutoff
    (a b c d : ℝ) (hab : a ≤ b) :
    fullTimeBandFourier a b c d hab = cutoffFourierCutoff a b c d := by
  ext f
  let g : SoninL2 := indicatorCutoff (Set.Icc c d) measurableSet_Icc f
  have hgInt : Integrable (g : ℝ → ℂ) := integrable_indicatorCutoff_Icc c d f
  have hfourier : (fourierUnitary g : ℝ → ℂ) =ᵐ[volume]
      (Lp.fourierTransform ((memLp_one_iff_integrable.mpr hgInt).toLp g) : ℝ → ℂ) := by
    simpa [fourierUnitary] using l2_fourier_coeFn_eq_l1_fourier_of_integrable g hgInt
  ext1
  filter_upwards [fullTimeBandFourier_coeFn_sonin a b c d hab f,
    indicatorCutoff_ae (Set.Icc a b) measurableSet_Icc (fourierUnitary g),
    hfourier] with x hfull hcut hfourierx
  change fullTimeBandFourier a b c d hab f x =
    indicatorCutoff (Set.Icc a b) measurableSet_Icc (fourierUnitary g) x
  rw [hfull, hcut]
  by_cases hx : x ∈ Set.Icc a b
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hfourierx,
      l1Fourier_indicatorCutoff_Icc_eq_setIntegral c d f x]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

theorem isCompactOperator_cutoffFourierCutoff
    (a b c d : ℝ) (hab : a ≤ b) :
    IsCompactOperator (cutoffFourierCutoff a b c d) := by
  rw [← fullTimeBandFourier_eq_cutoffFourierCutoff a b c d hab]
  exact isCompactOperator_fullTimeBandFourier a b c d hab

def closedEvenShell (a b : ℝ) : Set ℝ :=
  Set.Icc (-b) (-a) ∪ Set.Icc a b

theorem measurableSet_closedEvenShell (a b : ℝ) : MeasurableSet (closedEvenShell a b) :=
  measurableSet_Icc.union measurableSet_Icc

theorem indicatorCutoff_closedEvenShell_eq_add
    (a b : ℝ) (ha : 0 < a) :
    indicatorCutoff (closedEvenShell a b) (measurableSet_closedEvenShell a b) =
      indicatorCutoff (Set.Icc (-b) (-a)) measurableSet_Icc +
        indicatorCutoff (Set.Icc a b) measurableSet_Icc := by
  ext f
  ext1
  filter_upwards [
    indicatorCutoff_ae (closedEvenShell a b) (measurableSet_closedEvenShell a b) f,
    indicatorCutoff_ae (Set.Icc (-b) (-a)) measurableSet_Icc f,
    indicatorCutoff_ae (Set.Icc a b) measurableSet_Icc f,
    Lp.coeFn_add
      (indicatorCutoff (Set.Icc (-b) (-a)) measurableSet_Icc f)
      (indicatorCutoff (Set.Icc a b) measurableSet_Icc f)
  ] with x hshell hneg hpos hadd
  rw [hshell, hadd, hneg, hpos]
  by_cases hn : x ∈ Set.Icc (-b) (-a)
  · have hp : x ∉ Set.Icc a b := by
      intro hp
      nlinarith [hn.2, hp.1]
    simp [closedEvenShell, hn, hp]
  · by_cases hp : x ∈ Set.Icc a b <;> simp [closedEvenShell, hn, hp]

def shellCutoffFourierCutoff (a b : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc ∘L
    fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    indicatorCutoff (closedEvenShell a b) (measurableSet_closedEvenShell a b)

theorem shellCutoffFourierCutoff_eq_add (a b : ℝ) (ha : 0 < a) :
    shellCutoffFourierCutoff a b =
      cutoffFourierCutoff (-a) a (-b) (-a) + cutoffFourierCutoff (-a) a a b := by
  rw [shellCutoffFourierCutoff, indicatorCutoff_closedEvenShell_eq_add a b ha]
  ext f
  simp [cutoffFourierCutoff]

theorem isCompactOperator_shellCutoffFourierCutoff
    (a b : ℝ) (ha : 0 < a) :
    IsCompactOperator (shellCutoffFourierCutoff a b) := by
  rw [shellCutoffFourierCutoff_eq_add a b ha]
  exact (isCompactOperator_cutoffFourierCutoff (-a) a (-b) (-a) (by nlinarith)).add
    (isCompactOperator_cutoffFourierCutoff (-a) a a b (by nlinarith))

def reflectionIsometry : SoninL2 →ₗᵢ[ℂ] SoninL2 :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x)
    (Measure.measurePreserving_neg (volume : Measure ℝ))

def reflection : SoninL2 →L[ℂ] SoninL2 :=
  reflectionIsometry.toContinuousLinearMap

theorem fourierUnitary_reflection (f : SoninL2) :
    fourierUnitary (reflection f) = reflection (fourierUnitary f) := by
  simpa [fourierUnitary, reflection, reflectionIsometry, l2Reflection,
    l2ReflectionIsometry] using l2_fourier_reflection f

theorem reflection_ae (f : SoninL2) :
    reflection f =ᵐ[volume] fun x : ℝ => f (-x) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (Measure.measurePreserving_neg (volume : Measure ℝ))

@[simp] theorem reflection_reflection (f : SoninL2) : reflection (reflection f) = f := by
  ext1
  filter_upwards [reflection_ae (reflection f), reflection_ae f] with x hRf hf
  rw [hRf, hf]
  simp

theorem reflection_symmetric : reflection.toLinearMap.IsSymmetric := by
  intro f g
  rw [← reflectionIsometry.inner_map_map]
  simp only [reflection, reflectionIsometry, LinearIsometry.coe_toContinuousLinearMap,
    reflection_reflection]

def evenProjection : SoninL2 →L[ℂ] SoninL2 :=
  (2 : ℂ)⁻¹ • ((1 : SoninL2 →L[ℂ] SoninL2) + reflection)

@[simp] theorem evenProjection_apply (f : SoninL2) :
    evenProjection f = (2 : ℂ)⁻¹ • (f + reflection f) := rfl

@[simp] theorem reflection_evenProjection (f : SoninL2) :
    reflection (evenProjection f) = evenProjection f := by
  simp [evenProjection_apply, map_add, map_smul]

theorem evenProjection_idempotent : IsIdempotentElem evenProjection := by
  rw [isIdempotentElem_iff]
  ext f
  simp

theorem evenProjection_symmetric : evenProjection.toLinearMap.IsSymmetric := by
  exact (LinearMap.isSymmetric_id ℂ SoninL2).add reflection_symmetric |>.smul (by norm_num)

theorem evenProjection_isStarProjection : IsStarProjection evenProjection := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨evenProjection_idempotent.toLinearMap, evenProjection_symmetric⟩

def evenSubspace : Submodule ℂ SoninL2 := LinearMap.range evenProjection.toLinearMap

instance : evenSubspace.HasOrthogonalProjection :=
  evenProjection_isStarProjection.isSymmetricProjection.hasOrthogonalProjection_range

theorem evenProjection_eq_starProjection :
    evenProjection = evenSubspace.starProjection :=
  (ContinuousLinearMap.isStarProjection_iff_eq_starProjection_range.mp
    evenProjection_isStarProjection).2

theorem mem_evenSubspace_iff (f : SoninL2) :
    f ∈ evenSubspace ↔ reflection f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact reflection_evenProjection g
  · intro hf
    refine ⟨f, ?_⟩
    simp [evenProjection_apply, hf]

theorem memLp_comp_mul (a : ℝ) (ha : a ≠ 0) (f : SoninL2) :
    MemLp (fun x : ℝ => f (a * x)) 2 (volume : Measure ℝ) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv
  have hmap : Measure.map (fun x : ℝ => a * x) volume =
      ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ) := Real.map_volume_mul_left ha
  have hfscaled : MemLp (fun x : ℝ => f x) 2
      (Measure.map (fun x : ℝ => a * x) volume) := by
    rw [hmap]
    exact (Lp.memLp f).smul_measure (by simp)
  exact (e.memLp_map_measure_iff (g := fun x : ℝ => f x) (p := 2)
    (μ := volume)).mp hfscaled

def rawDilationAux (a : ℝ) (ha : a ≠ 0) (f : SoninL2) : SoninL2 :=
  MemLp.toLp (fun x : ℝ => f (a * x)) (memLp_comp_mul a ha f)

theorem rawDilationAux_ae (a : ℝ) (ha : a ≠ 0) (f : SoninL2) :
    rawDilationAux a ha f =ᵐ[volume] fun x : ℝ => f (a * x) :=
  MemLp.coeFn_toLp (memLp_comp_mul a ha f)

def rawDilationLinear (a : ℝ) (ha : a ≠ 0) : SoninL2 →ₗ[ℂ] SoninL2 where
  toFun := rawDilationAux a ha
  map_add' f g := by
    ext1
    filter_upwards [rawDilationAux_ae a ha (f + g), rawDilationAux_ae a ha f,
      rawDilationAux_ae a ha g, Lp.coeFn_add f g,
      Lp.coeFn_add (rawDilationAux a ha f) (rawDilationAux a ha g)] with x hfg hf hg hadd hadd'
    rw [hfg, hadd']
    simp only [Pi.add_apply, hf, hg, hadd]
  map_smul' c f := by
    ext1
    filter_upwards [rawDilationAux_ae a ha (c • f), rawDilationAux_ae a ha f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (rawDilationAux a ha f)] with x hcf hf hsmul hsmul'
    rw [hcf, hsmul']
    simp only [Pi.smul_apply, hf, hsmul]

theorem eLpNorm_rawDilation (a : ℝ) (ha : a ≠ 0) (f : SoninL2) :
    eLpNorm (fun x : ℝ => f (a * x)) 2 volume =
      ENNReal.ofReal |a⁻¹| ^ (2 : ℝ≥0∞).toReal⁻¹ * eLpNorm (fun x : ℝ => f x) 2 volume := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv
  calc
    eLpNorm (fun x : ℝ => f (a * x)) 2 volume =
        eLpNorm (fun x : ℝ => f x) 2 (Measure.map (fun x : ℝ => a * x) volume) := by
      symm
      exact e.measurableEmbedding.eLpNorm_map_measure
    _ = eLpNorm (fun x : ℝ => f x) 2
        (ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ)) := by
      rw [Real.map_volume_mul_left ha]
    _ = _ := by
      rw [eLpNorm_smul_measure_of_ne_zero]
      · simp only [smul_eq_mul]
      · simp [ha]

theorem norm_rawDilationAux (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    ‖rawDilationAux a ha.ne' f‖ = (Real.sqrt a)⁻¹ * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (rawDilationAux_ae a ha.ne' f),
    eLpNorm_rawDilation a ha.ne' f, ENNReal.toReal_mul]
  congr 1
  rw [ENNReal.toReal_rpow]
  norm_num
  rw [abs_of_pos ha, inv_eq_one_div, ENNReal.toReal_ofReal (by positivity)]
  rw [show (1 / a) ^ (1 / 2 : ℝ) = (Real.sqrt a)⁻¹ by
    rw [one_div, Real.inv_rpow (le_of_lt ha)]
    congr
    rw [← Real.sqrt_eq_rpow]]

def dilation (a : ℝ) (ha : 0 < a) : SoninL2 →ₗᵢ[ℂ] SoninL2 where
  toLinearMap := (Real.sqrt a : ℂ) • rawDilationLinear a ha.ne'
  norm_map' f := by
    simp only [LinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_sqrt (le_of_lt ha), norm_rawDilationAux a ha f]
    rw [mul_assoc, Real.mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr ha.ne')]
    simp

theorem dilation_ae (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    dilation a ha f =ᵐ[volume] fun x : ℝ => (Real.sqrt a : ℂ) * f (a * x) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt a : ℂ) (rawDilationAux a ha.ne' f),
    rawDilationAux_ae a ha.ne' f] with x hsmul hraw
  rw [hsmul, hraw]
  rfl

theorem sqrt_mul_sqrt_inv (a : ℝ) (ha : 0 < a) :
    Real.sqrt a * Real.sqrt a⁻¹ = 1 := by
  rw [Real.sqrt_inv (le_of_lt ha), mul_inv_cancel₀]
  exact Real.sqrt_ne_zero'.mpr ha.ne'

@[simp] theorem dilation_dilation_inv (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    dilation a ha (dilation a⁻¹ (inv_pos.mpr ha) f) = f := by
  ext1
  have hcomp := (dilation_ae a⁻¹ (inv_pos.mpr ha) f).comp_tendsto
    (Real.quasiMeasurePreserving_smul (volume : Measure ℝ) ha.ne').tendsto_ae
  filter_upwards [dilation_ae a ha (dilation a⁻¹ (inv_pos.mpr ha) f), hcomp] with x hout hin
  rw [hout, hin]
  simp only [smul_eq_mul]
  push_cast
  rw [← mul_assoc, Complex.ofReal_mul, sqrt_mul_sqrt_inv a ha]
  simp [ha.ne']

@[simp] theorem dilation_inv_dilation (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    dilation a⁻¹ (inv_pos.mpr ha) (dilation a ha f) = f := by
  have hi : 0 < a⁻¹ := inv_pos.mpr ha
  convert dilation_dilation_inv a⁻¹ hi f using 1
  simp [ha.ne']

def dilationUnitary (a : ℝ) (ha : 0 < a) : SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  LinearIsometryEquiv.ofSurjective (dilation a ha) fun f =>
    ⟨dilation a⁻¹ (inv_pos.mpr ha) f, dilation_dilation_inv a ha f⟩

@[simp] theorem dilationUnitary_apply (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    dilationUnitary a ha f = dilation a ha f := rfl

@[simp] theorem dilationUnitary_symm_apply (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    (dilationUnitary a ha).symm f = dilation a⁻¹ (inv_pos.mpr ha) f := by
  apply (dilationUnitary a ha).injective
  simp

def dilationCLM (a : ℝ) (ha : 0 < a) : SoninL2 →L[ℂ] SoninL2 :=
  (dilationUnitary a ha : SoninL2 →L[ℂ] SoninL2)

@[simp] theorem dilationCLM_apply (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    dilationCLM a ha f = dilation a ha f := rfl

theorem adjoint_dilationCLM (a : ℝ) (ha : 0 < a) :
    (dilationCLM a ha)† = dilationCLM a⁻¹ (inv_pos.mpr ha) := by
  rw [dilationCLM, LinearIsometryEquiv.adjoint_eq_symm]
  ext f
  simp

def normalizedIndicator (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) : SoninL2 :=
  ((Real.sqrt (volume.real s))⁻¹ : ℂ) • indicatorConstLp 2 hs hfin (1 : ℂ)

theorem normalizedIndicator_ae (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) :
    normalizedIndicator s hs hfin =ᵐ[volume]
      fun x : ℝ => ((Real.sqrt (volume.real s))⁻¹ : ℂ) * s.indicator (fun _ => (1 : ℂ)) x := by
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (volume.real s))⁻¹ : ℂ)
      (indicatorConstLp 2 hs hfin (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := volume) (c := (1 : ℂ))] with x hsmul hind
  rw [hsmul, hind]
  rfl

theorem norm_normalizedIndicator (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (hpos : 0 < volume.real s) :
    ‖normalizedIndicator s hs hfin‖ = 1 := by
  simp only [normalizedIndicator, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_sqrt (le_of_lt hpos)]
  rw [norm_indicatorConstLp (p := 2) (μ := volume) (by norm_num) (by norm_num)]
  norm_num
  rw [show (volume.real s) ^ (1 / (2 : ℝ)) = Real.sqrt (volume.real s) by
    rw [Real.sqrt_eq_rpow]]
  rw [inv_mul_cancel₀]
  exact Real.sqrt_ne_zero'.mpr hpos.ne'

theorem inner_normalizedIndicator_eq_zero {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : volume s ≠ ∞) (hft : volume t ≠ ∞) (hst : Disjoint s t) :
    inner ℂ (normalizedIndicator s hs hfs) (normalizedIndicator t ht hft) = 0 := by
  simp only [normalizedIndicator, inner_smul_left, inner_smul_right]
  rw [MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one hs ht hfs hft]
  rw [hst.inter_eq, measureReal_empty]
  simp

theorem orthonormal_normalizedIndicator {ι : Type*} {s : ι → Set ℝ}
    (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, volume (s i) ≠ ∞)
    (hpos : ∀ i, 0 < volume.real (s i)) (hdisj : Set.PairwiseDisjoint Set.univ s) :
    Orthonormal ℂ (fun i => normalizedIndicator (s i) (hs i) (hfin i)) := by
  constructor
  · intro i
    exact norm_normalizedIndicator (s i) (hs i) (hfin i) (hpos i)
  · intro i j hij
    exact inner_normalizedIndicator_eq_zero (hs i) (hs j) (hfin i) (hfin j)
      (hdisj (Set.mem_univ i) (Set.mem_univ j) hij)

def shellLeft (a b : ℝ) (n : ℕ) : ℝ :=
  a + (b - a) / ((n : ℝ) + 3)

def shellRight (a b : ℝ) (n : ℕ) : ℝ :=
  a + (b - a) / ((n : ℝ) + 2)

def shellCell (a b : ℝ) (n : ℕ) : Set ℝ :=
  Set.Ioc (shellLeft a b n) (shellRight a b n)

def evenShellCell (a b : ℝ) (n : ℕ) : Set ℝ :=
  (fun x : ℝ => |x|) ⁻¹' shellCell a b n

theorem shellLeft_lt_shellRight {a b : ℝ} (hab : a < b) (n : ℕ) :
    shellLeft a b n < shellRight a b n := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have h2 : 0 < (n : ℝ) + 2 := by positivity
  have h3 : 0 < (n : ℝ) + 3 := by positivity
  have hdiv : (b - a) / ((n : ℝ) + 3) < (b - a) / ((n : ℝ) + 2) := by
    rw [div_lt_div_iff₀ h3 h2]
    nlinarith
  simpa [shellLeft, shellRight] using add_lt_add_left hdiv a

theorem shellLeft_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    0 < shellLeft a b n := by
  have : 0 < (b - a) / ((n : ℝ) + 3) := div_pos (sub_pos.mpr hab) (by positivity)
  simp only [shellLeft]
  linarith

theorem lt_shellLeft {a b : ℝ} (hab : a < b) (n : ℕ) :
    a < shellLeft a b n := by
  have : 0 < (b - a) / ((n : ℝ) + 3) := div_pos (sub_pos.mpr hab) (by positivity)
  simpa [shellLeft] using add_lt_add_left this a

theorem shellRight_lt {a b : ℝ} (hab : a < b) (n : ℕ) :
    shellRight a b n < b := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hden : 2 ≤ (n : ℝ) + 2 := by positivity
  have hfrac : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / 2 := by
    exact div_le_div_of_nonneg_left hd.le (by norm_num) hden
  have hhalf : (b - a) / 2 < b - a := by linarith
  simp only [shellRight]
  linarith

theorem shellCell_disjoint_of_lt {a b : ℝ} (hab : a < b) {m n : ℕ} (hmn : m < n) :
    Disjoint (shellCell a b m) (shellCell a b n) := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hcast : (m : ℝ) + 3 ≤ (n : ℝ) + 2 := by
    exact_mod_cast (Nat.add_le_add_right (Nat.succ_le_iff.mpr hmn) 2)
  have hm3 : 0 < (m : ℝ) + 3 := by positivity
  have hn2 : 0 < (n : ℝ) + 2 := by positivity
  have hfrac : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / ((m : ℝ) + 3) := by
    exact div_le_div_of_nonneg_left hd.le hm3 hcast
  have hsep : shellRight a b n ≤ shellLeft a b m := by
    simpa [shellRight, shellLeft] using add_le_add_left hfrac a
  exact (Ioc_disjoint_Ioc_of_le hsep).symm

theorem shellCell_pairwiseDisjoint {a b : ℝ} (hab : a < b) :
    Set.PairwiseDisjoint Set.univ (shellCell a b) := by
  intro m _ n _ hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact shellCell_disjoint_of_lt hab h
  · exact (shellCell_disjoint_of_lt hab h).symm

theorem evenShellCell_pairwiseDisjoint {a b : ℝ} (hab : a < b) :
    Set.PairwiseDisjoint Set.univ (evenShellCell a b) := by
  intro m _ n _ hmn
  exact Disjoint.preimage (fun x : ℝ => |x|)
    (shellCell_pairwiseDisjoint hab (Set.mem_univ m) (Set.mem_univ n) hmn)

theorem measurableSet_evenShellCell (a b : ℝ) (n : ℕ) :
    MeasurableSet (evenShellCell a b n) := by
  exact measurableSet_Ioc.preimage (continuous_abs.measurable)

theorem shellCell_subset_evenShellCell {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    shellCell a b n ⊆ evenShellCell a b n := by
  intro x hx
  change |x| ∈ shellCell a b n
  have hxpos : 0 < x := (shellLeft_pos ha hab n).trans_le hx.1
  simpa [abs_of_pos hxpos] using hx

theorem evenShellCell_subset_Icc {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    evenShellCell a b n ⊆ Set.Icc (-b) b := by
  intro x hx
  have habs : |x| < b := hx.2.trans_lt (shellRight_lt hab n)
  exact (abs_lt.mp habs).le

theorem evenShellCell_measure_ne_top {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    volume (evenShellCell a b n) ≠ ∞ :=
  measure_ne_top_of_subset (evenShellCell_subset_Icc ha hab n) (by finiteness)

theorem evenShellCell_measureReal_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    0 < volume.real (evenShellCell a b n) := by
  have hcellpos : volume (shellCell a b n) ≠ 0 := by
    rw [shellCell, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_zero.mpr (sub_pos.mpr (shellLeft_lt_shellRight hab n)).ne'
  have hevenpos : volume (evenShellCell a b n) ≠ 0 := by
    intro hzero
    have hle := measure_mono (shellCell_subset_evenShellCell ha hab n)
    rw [hzero] at hle
    exact hcellpos (bot_unique hle)
  exact lt_of_le_of_ne measureReal_nonneg
    ((measureReal_ne_zero_iff (evenShellCell_measure_ne_top ha hab n)).mpr hevenpos).symm

def evenShellVector (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) : SoninL2 :=
  normalizedIndicator (evenShellCell a b n) (measurableSet_evenShellCell a b n)
    (evenShellCell_measure_ne_top ha hab n)

theorem evenShellVector_orthonormal (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Orthonormal ℂ (evenShellVector a b ha hab) := by
  exact orthonormal_normalizedIndicator (measurableSet_evenShellCell a b)
    (evenShellCell_measure_ne_top ha hab) (evenShellCell_measureReal_pos ha hab)
    (evenShellCell_pairwiseDisjoint hab)

theorem reflection_evenShellVector (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    reflection (evenShellVector a b ha hab n) = evenShellVector a b ha hab n := by
  ext1
  let s := evenShellCell a b n
  let hs := measurableSet_evenShellCell a b n
  let hfin := evenShellCell_measure_ne_top ha hab n
  have hneg := (normalizedIndicator_ae s hs hfin).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [reflection_ae (evenShellVector a b ha hab n), hneg,
    normalizedIndicator_ae s hs hfin] with x href hnegx hx
  rw [href]
  change normalizedIndicator s hs hfin (-x) = normalizedIndicator s hs hfin x
  rw [hnegx, hx]
  simp only [s, evenShellCell, shellCell, abs_neg]

theorem evenShellVector_mem_evenSubspace (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    evenShellVector a b ha hab n ∈ evenSubspace :=
  (mem_evenSubspace_iff _).mpr (reflection_evenShellVector a b ha hab n)

theorem indicatorCutoff_dilation_normalizedIndicator_eq_self
    (c s : Set ℝ) (hc : MeasurableSet c) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (p : ℝ) (hp : 0 < p)
    (hsub : (fun x : ℝ => p * x) ⁻¹' s ⊆ c) :
    indicatorCutoff c hc (dilation p hp (normalizedIndicator s hs hfin)) =
      dilation p hp (normalizedIndicator s hs hfin) := by
  ext1
  have hnormcomp := (normalizedIndicator_ae s hs hfin).comp_tendsto
    (Real.quasiMeasurePreserving_smul (volume : Measure ℝ) hp.ne').tendsto_ae
  filter_upwards [indicatorCutoff_ae c hc (dilation p hp (normalizedIndicator s hs hfin)),
    dilation_ae p hp (normalizedIndicator s hs hfin), hnormcomp] with x hcut hdil hnorm
  rw [hcut, hdil]
  by_cases hxs : p * x ∈ s
  · rw [Set.indicator_of_mem (hsub hxs)]
  · rw [hnorm, Set.indicator_of_notMem hxs]
    simp

theorem indicatorCutoff_dilation_normalizedIndicator_eq_zero
    (c s : Set ℝ) (hc : MeasurableSet c) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (p : ℝ) (hp : 0 < p)
    (hdisj : Disjoint c ((fun x : ℝ => p * x) ⁻¹' s)) :
    indicatorCutoff c hc (dilation p hp (normalizedIndicator s hs hfin)) = 0 := by
  ext1
  have hnormcomp := (normalizedIndicator_ae s hs hfin).comp_tendsto
    (Real.quasiMeasurePreserving_smul (volume : Measure ℝ) hp.ne').tendsto_ae
  filter_upwards [indicatorCutoff_ae c hc (dilation p hp (normalizedIndicator s hs hfin)),
    dilation_ae p hp (normalizedIndicator s hs hfin), hnormcomp] with x hcut hdil hnorm
  rw [hcut]
  by_cases hxc : x ∈ c
  · have hxnot : p * x ∉ s := fun hxs => Set.disjoint_left.1 hdisj hxc hxs
    rw [Set.indicator_of_mem hxc, hdil, hnorm, Set.indicator_of_notMem hxnot]
    simp
  · rw [Set.indicator_of_notMem hxc]

theorem inward_shell_preimage_subset (a p : ℝ) (ha : 0 < a) (hp : 1 < p) (n : ℕ) :
    (fun x : ℝ => p * x) ⁻¹' evenShellCell a (p * a) n ⊆ Set.Icc (-a) a := by
  intro x hx
  have hpa : a < p * a := by nlinarith
  have habs_scaled : |p * x| < p * a := hx.2.trans_lt (shellRight_lt hpa n)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have habs : |x| < a := by
    apply (mul_lt_mul_left hp0).mp
    simpa [abs_mul, abs_of_pos hp0] using habs_scaled
  exact (abs_lt.mp habs).le

theorem outward_shell_preimage_disjoint (a p : ℝ) (ha : 0 < a) (hp : 1 < p) (n : ℕ) :
    Disjoint (Set.Icc (-a) a)
      ((fun x : ℝ => p⁻¹ * x) ⁻¹' evenShellCell a (p * a) n) := by
  rw [Set.disjoint_left]
  intro x hxc hxs
  have hpa : a < p * a := by nlinarith
  have hxabs : |x| ≤ a := abs_le.mpr hxc
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hinv0 : 0 < p⁻¹ := inv_pos.mpr hp0
  have hinv_le : p⁻¹ ≤ 1 := inv_le_one₀ hp0.le hp.le
  have hscaled_le : |p⁻¹ * x| ≤ a := by
    rw [abs_mul, abs_of_pos hinv0]
    calc
      p⁻¹ * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right hinv_le (abs_nonneg x)
      _ ≤ a := by simpa using hxabs
  have hscaled_gt : a < |p⁻¹ * x| := (lt_shellLeft hpa n).trans hxs.1
  exact (not_lt_of_ge hscaled_le) hscaled_gt

theorem physicalCutoff_evenShellCell_disjoint (a p : ℝ) (ha : 0 < a)
    (hp : 1 < p) (n : ℕ) :
    Disjoint (Set.Icc (-a) a) (evenShellCell a (p * a) n) := by
  rw [Set.disjoint_left]
  intro x hxc hxs
  have hpa : a < p * a := by nlinarith
  have hxabs : |x| ≤ a := abs_le.mpr hxc
  have hshell : a < |x| := (lt_shellLeft hpa n).trans hxs.1
  exact (not_lt_of_ge hxabs) hshell

theorem evenShellCell_subset_closedEvenShell
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    evenShellCell a b n ⊆ closedEvenShell a b := by
  intro x hx
  have hlower : a < |x| := (lt_shellLeft hab n).trans hx.1
  have hupper : |x| < b := hx.2.trans_lt (shellRight_lt hab n)
  by_cases hxnonneg : 0 ≤ x
  · right
    simpa [abs_of_nonneg hxnonneg] using ⟨hlower.le, hupper.le⟩
  · left
    have hxneg : x < 0 := lt_of_not_ge hxnonneg
    have hbounds : a ≤ -x ∧ -x ≤ b := by
      simpa [abs_of_neg hxneg] using ⟨hlower.le, hupper.le⟩
    constructor <;> linarith

theorem shellCutoff_evenShellVector (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (n : ℕ) :
    indicatorCutoff (closedEvenShell a b) (measurableSet_closedEvenShell a b)
      (evenShellVector a b ha hab n) = evenShellVector a b ha hab n := by
  ext1
  filter_upwards [
    indicatorCutoff_ae (closedEvenShell a b) (measurableSet_closedEvenShell a b)
      (evenShellVector a b ha hab n),
    normalizedIndicator_ae (evenShellCell a b n)
      (measurableSet_evenShellCell a b n)
      (evenShellCell_measure_ne_top ha hab n)
  ] with x hcut hshell
  rw [hcut, hshell]
  by_cases hx : x ∈ evenShellCell a b n
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem (evenShellCell_subset_closedEvenShell ha hab n hx)]
  · rw [Set.indicator_of_notMem hx]
    simp

theorem physicalCutoff_evenShellVector (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (n : ℕ) :
    indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
      (evenShellVector a (p * a) ha (by nlinarith) n) = 0 := by
  ext1
  filter_upwards [indicatorCutoff_ae (Set.Icc (-a) a) measurableSet_Icc
      (evenShellVector a (p * a) ha (by nlinarith) n),
    normalizedIndicator_ae (evenShellCell a (p * a) n)
      (measurableSet_evenShellCell a (p * a) n)
      (evenShellCell_measure_ne_top ha (by nlinarith) n)] with x hcut hshell
  rw [hcut]
  by_cases hxc : x ∈ Set.Icc (-a) a
  · have hxnot : x ∉ evenShellCell a (p * a) n := fun hxs =>
      Set.disjoint_left.1 (physicalCutoff_evenShellCell_disjoint a p ha hp n) hxc hxs
    rw [Set.indicator_of_mem hxc, hshell, Set.indicator_of_notMem hxnot]
    simp
  · rw [Set.indicator_of_notMem hxc]

theorem evenShellVector_mem_physicalForbidden_orthogonal
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) (n : ℕ) :
    evenShellVector a (p * a) ha (by nlinarith) n ∈
      (physicalForbidden (Set.Icc (-a) a) measurableSet_Icc)ᗮ := by
  apply (Submodule.starProjection_apply_eq_zero_iff).mp
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
  exact physicalCutoff_evenShellVector a p ha hp n

theorem physicalCutoff_inward_evenShellVector (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (n : ℕ) :
    indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
        (dilation p (zero_lt_one.trans hp) (evenShellVector a (p * a) ha (by nlinarith) n)) =
      dilation p (zero_lt_one.trans hp) (evenShellVector a (p * a) ha (by nlinarith) n) := by
  apply indicatorCutoff_dilation_normalizedIndicator_eq_self
  exact inward_shell_preimage_subset a p ha hp n

theorem physicalCutoff_outward_evenShellVector (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (n : ℕ) :
    indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
        (dilation p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
          (evenShellVector a (p * a) ha (by nlinarith) n)) = 0 := by
  apply indicatorCutoff_dilation_normalizedIndicator_eq_zero
  exact outward_shell_preimage_disjoint a p ha hp n

def dilationSum (p : ℝ) (hp : 1 < p) : SoninL2 →L[ℂ] SoninL2 :=
  dilationCLM p (zero_lt_one.trans hp) + (dilationCLM p (zero_lt_one.trans hp))†

@[simp] theorem dilationSum_apply (p : ℝ) (hp : 1 < p) (f : SoninL2) :
    dilationSum p hp f = dilation p (zero_lt_one.trans hp) f +
      dilation p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f := by
  rw [dilationSum, ContinuousLinearMap.add_apply, adjoint_dilationCLM]
  rfl

theorem physicalCutoff_dilationSum_evenShellVector (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (n : ℕ) :
    indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
        (dilationSum p hp (evenShellVector a (p * a) ha (by nlinarith) n)) =
      dilation p (zero_lt_one.trans hp) (evenShellVector a (p * a) ha (by nlinarith) n) := by
  rw [dilationSum_apply, map_add, physicalCutoff_inward_evenShellVector,
    physicalCutoff_outward_evenShellVector, add_zero]

theorem norm_physicalCutoff_dilationSum_evenShellVector (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (n : ℕ) :
    ‖indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
        (dilationSum p hp (evenShellVector a (p * a) ha (by nlinarith) n))‖ = 1 := by
  rw [physicalCutoff_dilationSum_evenShellVector]
  exact (dilation p (zero_lt_one.trans hp)).norm_map.trans
    ((evenShellVector_orthonormal a (p * a) ha (by nlinarith)).norm_eq_one n)

/-! ### Restricted-measure L² and zero extension -/

abbrev RestrictedL2 (s : Set ℝ) := Lp ℂ 2 ((volume : Measure ℝ).restrict s)

def restrictL2 (s : Set ℝ) : SoninL2 →L[ℂ] RestrictedL2 s :=
  LpToLpRestrictCLM ℝ ℂ ℂ (volume : Measure ℝ) 2 s

theorem restrictL2_ae (s : Set ℝ) (f : SoninL2) :
    restrictL2 s f =ᵐ[(volume : Measure ℝ).restrict s] fun x : ℝ => f x :=
  LpToLpRestrictCLM_coeFn (μ := (volume : Measure ℝ)) (p := (2 : ENNReal)) ℂ s f

def extendL2 (s : Set ℝ) (hs : MeasurableSet s) : RestrictedL2 s →ₗᵢ[ℂ] SoninL2 where
  toLinearMap := (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ)
    (volume : Measure ℝ) 2 s hs).toLinearMap
  norm_map' := norm_lpExtendByZero (F := ℂ) (𝕜 := ℂ)
    (volume : Measure ℝ) 2 s hs

theorem extendL2_ae (s : Set ℝ) (hs : MeasurableSet s) (f : RestrictedL2 s) :
    extendL2 s hs f =ᵐ[volume] s.indicator fun x : ℝ => f x :=
  lpExtendByZeroCLM_coeFn (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2 s hs f

@[simp] theorem restrictL2_extendL2 (s : Set ℝ) (hs : MeasurableSet s)
    (f : RestrictedL2 s) : restrictL2 s (extendL2 s hs f) = f := by
  ext1
  have hext_restrict : extendL2 s hs f =ᵐ[(volume : Measure ℝ).restrict s]
      s.indicator fun x : ℝ => f x :=
    (extendL2_ae s hs f).filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [restrictL2_ae s (extendL2 s hs f), hext_restrict,
    ae_restrict_mem measurableSet_mem] with x hres hext hxs
  rw [hres, hext, Set.indicator_of_mem hxs]

theorem extendL2_restrictL2 (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    extendL2 s hs (restrictL2 s f) = indicatorCutoff s hs f := by
  ext1
  have hres_on_s : ∀ᵐ x ∂volume, x ∈ s → restrictL2 s f x = f x :=
    (ae_restrict_iff' hs).mp (restrictL2_ae s f)
  filter_upwards [extendL2_ae s hs (restrictL2 s f), indicatorCutoff_ae s hs f,
    hres_on_s] with x hext hcut hres
  rw [hext, hcut]
  by_cases hxs : x ∈ s
  · simp [hxs, hres hxs]
  · simp [hxs]


attribute [local instance] Measure.Subtype.measureSpace

abbrev SubtypeL2 (s : Set ℝ) := Lp ℂ 2 (volume : Measure s)

def subtypeCoeMeasurePreserving (s : Set ℝ) (hs : MeasurableSet s) :
    MeasurePreserving ((↑) : s → ℝ) (volume : Measure s)
      ((volume : Measure ℝ).restrict s) := by
  refine ⟨measurable_subtype_coe, ?_⟩
  exact MeasurableSet.map_coe_volume hs

def restrictedToSubtype (s : Set ℝ) (hs : MeasurableSet s) :
    RestrictedL2 s →ₗᵢ[ℂ] SubtypeL2 s :=
  Lp.compMeasurePreservingₗᵢ ℂ ((↑) : s → ℝ) (subtypeCoeMeasurePreserving s hs)

def subtypeExtendFunction (s : Set ℝ) (f : SubtypeL2 s) : ℝ → ℂ :=
  Function.extend ((↑) : s → ℝ) (fun x => f x) 0

theorem memLp_subtypeExtendFunction_restrict (s : Set ℝ) (hs : MeasurableSet s)
    (f : SubtypeL2 s) :
    MemLp (subtypeExtendFunction s f) 2 ((volume : Measure ℝ).restrict s) := by
  rw [← MeasurableSet.map_coe_volume hs]
  apply (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff.mpr
  simpa [subtypeExtendFunction, Function.comp_def,
    Subtype.val_injective.extend_apply] using Lp.memLp f

def subtypeToRestrictedAux (s : Set ℝ) (hs : MeasurableSet s) (f : SubtypeL2 s) :
    RestrictedL2 s :=
  MemLp.toLp (subtypeExtendFunction s f) (memLp_subtypeExtendFunction_restrict s hs f)

theorem subtypeToRestrictedAux_ae (s : Set ℝ) (hs : MeasurableSet s) (f : SubtypeL2 s) :
    subtypeToRestrictedAux s hs f =ᵐ[(volume : Measure ℝ).restrict s]
      subtypeExtendFunction s f :=
  MemLp.coeFn_toLp (memLp_subtypeExtendFunction_restrict s hs f)

def subtypeToRestrictedLinear (s : Set ℝ) (hs : MeasurableSet s) :
    SubtypeL2 s →ₗ[ℂ] RestrictedL2 s where
  toFun := subtypeToRestrictedAux s hs
  map_add' f g := by
    ext1
    have hext_add : subtypeExtendFunction s (f + g) =ᵐ[(volume : Measure ℝ).restrict s]
        fun x => subtypeExtendFunction s f x + subtypeExtendFunction s g x := by
      apply (ae_restrict_iff_subtype hs).mpr
      filter_upwards [Lp.coeFn_add f g] with x hx
      simpa [subtypeExtendFunction, Subtype.val_injective.extend_apply] using hx
    filter_upwards [subtypeToRestrictedAux_ae s hs (f + g),
      subtypeToRestrictedAux_ae s hs f, subtypeToRestrictedAux_ae s hs g,
      hext_add, Lp.coeFn_add (subtypeToRestrictedAux s hs f)
        (subtypeToRestrictedAux s hs g)] with x hfg hf hg hext hadd
    rw [hfg, hadd, hext, hf, hg]
  map_smul' c f := by
    ext1
    have hext_smul : subtypeExtendFunction s (c • f) =ᵐ[(volume : Measure ℝ).restrict s]
        fun x => c • subtypeExtendFunction s f x := by
      apply (ae_restrict_iff_subtype hs).mpr
      filter_upwards [Lp.coeFn_smul c f] with x hx
      simpa [subtypeExtendFunction, Subtype.val_injective.extend_apply] using hx
    filter_upwards [subtypeToRestrictedAux_ae s hs (c • f),
      subtypeToRestrictedAux_ae s hs f, hext_smul,
      Lp.coeFn_smul c (subtypeToRestrictedAux s hs f)] with x hcf hf hext hsmul
    rw [hcf, hsmul, hext, hf]

theorem norm_subtypeToRestrictedAux (s : Set ℝ) (hs : MeasurableSet s) (f : SubtypeL2 s) :
    ‖subtypeToRestrictedAux s hs f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (subtypeToRestrictedAux_ae s hs f)]
  have hmap := (MeasurableEmbedding.subtype_coe hs).eLpNorm_map_measure
    (μ := (volume : Measure s)) (g := subtypeExtendFunction s f) (p := (2 : ENNReal))
  rw [MeasurableSet.map_coe_volume hs] at hmap
  rw [← hmap]
  congr 2
  funext x
  exact Subtype.val_injective.extend_apply (fun y : s => f y) 0 x

def subtypeToRestricted (s : Set ℝ) (hs : MeasurableSet s) :
    SubtypeL2 s →ₗᵢ[ℂ] RestrictedL2 s where
  toLinearMap := subtypeToRestrictedLinear s hs
  norm_map' := norm_subtypeToRestrictedAux s hs

@[simp] theorem restrictedToSubtype_subtypeToRestricted
    (s : Set ℝ) (hs : MeasurableSet s) (f : SubtypeL2 s) :
    restrictedToSubtype s hs (subtypeToRestricted s hs f) = f := by
  ext1
  filter_upwards [Lp.coeFn_compMeasurePreserving (subtypeToRestricted s hs f)
      (subtypeCoeMeasurePreserving s hs),
    (subtypeToRestrictedAux_ae s hs f).comp_tendsto
      (subtypeCoeMeasurePreserving s hs).tendsto_ae] with x hcomp hext
  rw [hcomp, hext]
  exact Subtype.val_injective.extend_apply (fun y : s => f y) 0 x

@[simp] theorem subtypeToRestricted_restrictedToSubtype
    (s : Set ℝ) (hs : MeasurableSet s) (f : RestrictedL2 s) :
    subtypeToRestricted s hs (restrictedToSubtype s hs f) = f := by
  ext1
  have hcomp_on_s : ∀ᵐ x ∂(volume : Measure ℝ).restrict s,
      subtypeExtendFunction s (restrictedToSubtype s hs f) x = f x := by
    apply (ae_restrict_iff_subtype hs).mpr
    filter_upwards [Lp.coeFn_compMeasurePreserving f
      (subtypeCoeMeasurePreserving s hs)] with x hx
    rw [subtypeExtendFunction, Subtype.val_injective.extend_apply]
    exact hx
  filter_upwards [subtypeToRestrictedAux_ae s hs (restrictedToSubtype s hs f),
    hcomp_on_s] with x hext hcomp
  rw [hext, hcomp]

def restrictedSubtypeEquiv (s : Set ℝ) (hs : MeasurableSet s) :
    RestrictedL2 s ≃ₗᵢ[ℂ] SubtypeL2 s where
  toLinearIsometry := restrictedToSubtype s hs
  invFun := subtypeToRestricted s hs
  left_inv := subtypeToRestricted_restrictedToSubtype s hs
  right_inv := restrictedToSubtype_subtypeToRestricted s hs

def toSubtypeL2 (s : Set ℝ) (hs : MeasurableSet s) :
    SoninL2 →L[ℂ] SubtypeL2 s :=
  (restrictedToSubtype s hs).toContinuousLinearMap ∘L restrictL2 s

theorem toSubtypeL2_ae (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    toSubtypeL2 s hs f =ᵐ[volume] fun x : s => f x := by
  have hres := (restrictL2_ae s f).comp_tendsto
    (subtypeCoeMeasurePreserving s hs).tendsto_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving (restrictL2 s f)
      (subtypeCoeMeasurePreserving s hs), hres] with x hcomp hresx
  rw [toSubtypeL2, ContinuousLinearMap.comp_apply, hcomp, hresx]
  rfl

def fromSubtypeL2 (s : Set ℝ) (hs : MeasurableSet s) :
    SubtypeL2 s →L[ℂ] SoninL2 :=
  (extendL2 s hs).toContinuousLinearMap ∘L
    (subtypeToRestricted s hs).toContinuousLinearMap

theorem fromSubtypeL2_ae (s : Set ℝ) (hs : MeasurableSet s) (f : SubtypeL2 s) :
    fromSubtypeL2 s hs f =ᵐ[volume] s.indicator (subtypeExtendFunction s f) := by
  exact extendL2_ae s hs (subtypeToRestricted s hs f)

@[simp] theorem toSubtypeL2_fromSubtypeL2
    (s : Set ℝ) (hs : MeasurableSet s) (f : SubtypeL2 s) :
    toSubtypeL2 s hs (fromSubtypeL2 s hs f) = f := by
  rw [toSubtypeL2, fromSubtypeL2]
  simp only [ContinuousLinearMap.comp_apply]
  rw [restrictL2_extendL2, restrictedToSubtype_subtypeToRestricted]

def localizedSubtypeOperator (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (K : SubtypeL2 s →L[ℂ] SubtypeL2 t) : SoninL2 →L[ℂ] SoninL2 :=
  fromSubtypeL2 t ht ∘L K ∘L toSubtypeL2 s hs

theorem isCompactOperator_localizedSubtypeOperator (s t : Set ℝ) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (K : SubtypeL2 s →L[ℂ] SubtypeL2 t)
    (hK : IsCompactOperator K) : IsCompactOperator (localizedSubtypeOperator s t hs ht K) :=
  (hK.comp_clm (toSubtypeL2 s hs)).clm_comp (fromSubtypeL2 t ht)

end RHTower
