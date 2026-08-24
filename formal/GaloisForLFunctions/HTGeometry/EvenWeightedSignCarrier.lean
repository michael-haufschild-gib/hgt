import GaloisForLFunctions.HTGeometry.WeightedDensityL2
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.HTGeometry.ModularFormationDoubleMeasures
import GaloisForLFunctions.RHTower.L2MellinUnitary
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

open MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

def signedWeightMeasure (w : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (realDensity fun t => |w t|)

abbrev SignedWeightL2 (w : ℝ → ℝ) := Lp ℂ 2 (signedWeightMeasure w)

theorem measurable_signedWeightDensity {w : ℝ → ℝ} (hw : Measurable w) :
    Measurable (realDensity fun t => |w t|) :=
  measurable_realDensity hw.abs

theorem map_neg_signedWeightMeasure {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    Measure.map (fun t : ℝ => -t) (signedWeightMeasure w) = signedWeightMeasure w := by
  rw [signedWeightMeasure,
    map_withDensity_of_involution measurable_neg (fun t => neg_neg t)
      (Measure.measurePreserving_neg (volume : Measure ℝ)).map_eq
      (measurable_signedWeightDensity hw)]
  congr 1
  funext t
  simp [realDensity, heven]

theorem measurePreserving_neg_signedWeightMeasure {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    MeasurePreserving (fun t : ℝ => -t) (signedWeightMeasure w) (signedWeightMeasure w) :=
  ⟨measurable_neg, map_neg_signedWeightMeasure hw heven⟩

def signedWeightReflection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    SignedWeightL2 w →L[ℂ] SignedWeightL2 w :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => -t)
    (measurePreserving_neg_signedWeightMeasure hw heven)).toContinuousLinearMap

theorem signedWeightReflection_ae {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : SignedWeightL2 w) :
    signedWeightReflection hw heven f =ᵐ[signedWeightMeasure w] fun t => f (-t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_neg_signedWeightMeasure hw heven)

@[simp] theorem signedWeightReflection_involutive {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : SignedWeightL2 w) :
    signedWeightReflection hw heven (signedWeightReflection hw heven f) = f := by
  apply Lp.ext
  have hinner := (signedWeightReflection_ae hw heven f).comp_tendsto
    (measurePreserving_neg_signedWeightMeasure hw heven).quasiMeasurePreserving.tendsto_ae
  filter_upwards [signedWeightReflection_ae hw heven (signedWeightReflection hw heven f),
    hinner] with t hout hin
  rw [hout]
  simpa [Function.comp_apply] using hin

theorem signedWeightReflection_symmetric {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    (signedWeightReflection hw heven).toLinearMap.IsSymmetric := by
  intro f g
  let U : SignedWeightL2 w →ₗᵢ[ℂ] SignedWeightL2 w :=
    Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => -t)
      (measurePreserving_neg_signedWeightMeasure hw heven)
  calc
    inner ℂ (signedWeightReflection hw heven f) g =
        inner ℂ (signedWeightReflection hw heven (signedWeightReflection hw heven f))
          (signedWeightReflection hw heven g) := by
      exact (U.inner_map_map (signedWeightReflection hw heven f) g).symm
    _ = inner ℂ f (signedWeightReflection hw heven g) := by
      rw [signedWeightReflection_involutive]

def signedWeightEvenProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) : SignedWeightL2 w →L[ℂ] SignedWeightL2 w :=
  (2 : ℂ)⁻¹ • ((1 : SignedWeightL2 w →L[ℂ] SignedWeightL2 w) +
    signedWeightReflection hw heven)

@[simp] theorem signedWeightEvenProjection_apply {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : SignedWeightL2 w) :
    signedWeightEvenProjection hw heven f =
      (2 : ℂ)⁻¹ • (f + signedWeightReflection hw heven f) := rfl

@[simp] theorem signedWeightReflection_evenProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : SignedWeightL2 w) :
    signedWeightReflection hw heven (signedWeightEvenProjection hw heven f) =
      signedWeightEvenProjection hw heven f := by
  simp [signedWeightEvenProjection_apply, map_add, map_smul, add_comm]

theorem signedWeightEvenProjection_idempotent {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    IsIdempotentElem (signedWeightEvenProjection hw heven) := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro f
  change signedWeightEvenProjection hw heven (signedWeightEvenProjection hw heven f) =
    signedWeightEvenProjection hw heven f
  rw [signedWeightEvenProjection_apply, signedWeightReflection_evenProjection]
  module

theorem signedWeightEvenProjection_symmetric {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    (signedWeightEvenProjection hw heven).toLinearMap.IsSymmetric := by
  apply (LinearMap.IsSymmetric.one.add (signedWeightReflection_symmetric hw heven)).smul
  change star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹
  rw [star_inv₀, star_ofNat]

theorem signedWeightEvenProjection_isStarProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    IsStarProjection (signedWeightEvenProjection hw heven) := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (signedWeightEvenProjection_idempotent hw heven),
    signedWeightEvenProjection_symmetric hw heven⟩

def signedWeightEvenSubspace {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) : Submodule ℂ (SignedWeightL2 w) :=
  LinearMap.range (signedWeightEvenProjection hw heven).toLinearMap

instance signedWeightEvenSubspace_completeSpace {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    CompleteSpace (signedWeightEvenSubspace hw heven) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (signedWeightEvenProjection_idempotent hw heven)).completeSpace_coe

theorem mem_signedWeightEvenSubspace_iff {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : SignedWeightL2 w) :
    f ∈ signedWeightEvenSubspace hw heven ↔ signedWeightReflection hw heven f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact signedWeightReflection_evenProjection hw heven g
  · intro hf
    refine ⟨f, ?_⟩
    change signedWeightEvenProjection hw heven f = f
    rw [signedWeightEvenProjection_apply, hf]
    module

theorem signedWeightReflection_lpBoundedMulCLM {w : ℝ → ℝ} (hw : Measurable w)
    (hweven : ∀ t, w (-t) = w t) {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖φ t‖ ≤ C) (hφeven : ∀ t, φ (-t) = φ t)
    (f : SignedWeightL2 w) :
    signedWeightReflection hw hweven
        (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC f) =
      lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC
        (signedWeightReflection hw hweven f) := by
  apply Lp.ext
  have hneg :=
    (lpBoundedMulCLM_coeFn (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC f).comp_tendsto
      (measurePreserving_neg_signedWeightMeasure hw hweven).quasiMeasurePreserving.tendsto_ae
  filter_upwards [
    signedWeightReflection_ae hw hweven
      (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC f),
    hneg,
    lpBoundedMulCLM_coeFn (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC
      (signedWeightReflection hw hweven f),
    signedWeightReflection_ae hw hweven f
  ] with t href hmul hright hf
  have hmul' :
      (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC f : ℝ → ℂ) (-t) =
        φ (-t) * (f : ℝ → ℂ) (-t) := by
    simpa [Function.comp_apply] using hmul
  rw [href, hmul', hφeven, hright, hf]

theorem signedWeightMul_mapsTo_evenSubspace {w : ℝ → ℝ} (hw : Measurable w)
    (hweven : ∀ t, w (-t) = w t) {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖φ t‖ ≤ C) (hφeven : ∀ t, φ (-t) = φ t) :
    Set.MapsTo (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC)
      (signedWeightEvenSubspace hw hweven) (signedWeightEvenSubspace hw hweven) := by
  intro f hf
  apply (mem_signedWeightEvenSubspace_iff hw hweven _).mpr
  rw [signedWeightReflection_lpBoundedMulCLM hw hweven hφ hC0 hC hφeven,
    (mem_signedWeightEvenSubspace_iff hw hweven f).mp hf]

def signedWeightEvenBoundedMul {w : ℝ → ℝ} (hw : Measurable w)
    (hweven : ∀ t, w (-t) = w t) {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖φ t‖ ≤ C) (hφeven : ∀ t, φ (-t) = φ t) :
    signedWeightEvenSubspace hw hweven →L[ℂ] signedWeightEvenSubspace hw hweven :=
  (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC).restrict
    (signedWeightMul_mapsTo_evenSubspace hw hweven hφ hC0 hC hφeven)

theorem signedWeightEvenBoundedMul_coeFn {w : ℝ → ℝ} (hw : Measurable w)
    (hweven : ∀ t, w (-t) = w t) {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖φ t‖ ≤ C) (hφeven : ∀ t, φ (-t) = φ t)
    (f : signedWeightEvenSubspace hw hweven) :
    (((signedWeightEvenBoundedMul hw hweven hφ hC0 hC hφeven f :
        signedWeightEvenSubspace hw hweven) : SignedWeightL2 w) : ℝ → ℂ)
      =ᵐ[signedWeightMeasure w] fun t => φ t * ((f : SignedWeightL2 w) : ℝ → ℂ) t :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := signedWeightMeasure w) hφ hC0 hC f

def weightFundamentalSymbol (w : ℝ → ℝ) (t : ℝ) : ℂ :=
  if w t < 0 then -1 else 1

def weightNegativeSymbol (w : ℝ → ℝ) (t : ℝ) : ℂ :=
  if w t < 0 then 1 else 0

def weightPositiveSymbol (w : ℝ → ℝ) (t : ℝ) : ℂ :=
  if 0 < w t then 1 else 0

theorem measurable_weightFundamentalSymbol {w : ℝ → ℝ} (hw : Measurable w) :
    Measurable (weightFundamentalSymbol w) := by
  unfold weightFundamentalSymbol
  exact Measurable.ite (measurableSet_lt hw measurable_const) measurable_const measurable_const

theorem measurable_weightNegativeSymbol {w : ℝ → ℝ} (hw : Measurable w) :
    Measurable (weightNegativeSymbol w) := by
  unfold weightNegativeSymbol
  exact Measurable.ite (measurableSet_lt hw measurable_const) measurable_const measurable_const

theorem measurable_weightPositiveSymbol {w : ℝ → ℝ} (hw : Measurable w) :
    Measurable (weightPositiveSymbol w) := by
  unfold weightPositiveSymbol
  exact Measurable.ite (measurableSet_lt measurable_const hw) measurable_const measurable_const

theorem norm_weightFundamentalSymbol_le (w : ℝ → ℝ) (t : ℝ) :
    ‖weightFundamentalSymbol w t‖ ≤ 1 := by
  unfold weightFundamentalSymbol
  split <;> norm_num

theorem norm_weightNegativeSymbol_le (w : ℝ → ℝ) (t : ℝ) :
    ‖weightNegativeSymbol w t‖ ≤ 1 := by
  unfold weightNegativeSymbol
  split <;> norm_num

theorem norm_weightPositiveSymbol_le (w : ℝ → ℝ) (t : ℝ) :
    ‖weightPositiveSymbol w t‖ ≤ 1 := by
  unfold weightPositiveSymbol
  split <;> norm_num

theorem weightFundamentalSymbol_even {w : ℝ → ℝ} (heven : ∀ t, w (-t) = w t) (t : ℝ) :
    weightFundamentalSymbol w (-t) = weightFundamentalSymbol w t := by
  simp [weightFundamentalSymbol, heven]

theorem weightNegativeSymbol_even {w : ℝ → ℝ} (heven : ∀ t, w (-t) = w t) (t : ℝ) :
    weightNegativeSymbol w (-t) = weightNegativeSymbol w t := by
  simp [weightNegativeSymbol, heven]

theorem weightPositiveSymbol_even {w : ℝ → ℝ} (heven : ∀ t, w (-t) = w t) (t : ℝ) :
    weightPositiveSymbol w (-t) = weightPositiveSymbol w t := by
  simp [weightPositiveSymbol, heven]

def weightFundamentalSymmetry {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    signedWeightEvenSubspace hw heven →L[ℂ] signedWeightEvenSubspace hw heven :=
  signedWeightEvenBoundedMul hw heven (measurable_weightFundamentalSymbol hw) (by norm_num)
    (norm_weightFundamentalSymbol_le w) (weightFundamentalSymbol_even heven)

def weightNegativeProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    signedWeightEvenSubspace hw heven →L[ℂ] signedWeightEvenSubspace hw heven :=
  signedWeightEvenBoundedMul hw heven (measurable_weightNegativeSymbol hw) (by norm_num)
    (norm_weightNegativeSymbol_le w) (weightNegativeSymbol_even heven)

def weightPositiveProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    signedWeightEvenSubspace hw heven →L[ℂ] signedWeightEvenSubspace hw heven :=
  signedWeightEvenBoundedMul hw heven (measurable_weightPositiveSymbol hw) (by norm_num)
    (norm_weightPositiveSymbol_le w) (weightPositiveSymbol_even heven)

theorem weightFundamentalSymmetry_coeFn {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : signedWeightEvenSubspace hw heven) :
    ((((weightFundamentalSymmetry hw heven) f : signedWeightEvenSubspace hw heven) :
        SignedWeightL2 w) : ℝ → ℂ) =ᵐ[signedWeightMeasure w]
      fun t => weightFundamentalSymbol w t * ((f : SignedWeightL2 w) : ℝ → ℂ) t :=
  signedWeightEvenBoundedMul_coeFn hw heven _ _ _ _ f

theorem weightNegativeProjection_coeFn {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : signedWeightEvenSubspace hw heven) :
    ((((weightNegativeProjection hw heven) f : signedWeightEvenSubspace hw heven) :
        SignedWeightL2 w) : ℝ → ℂ) =ᵐ[signedWeightMeasure w]
      fun t => weightNegativeSymbol w t * ((f : SignedWeightL2 w) : ℝ → ℂ) t :=
  signedWeightEvenBoundedMul_coeFn hw heven _ _ _ _ f

theorem weightPositiveProjection_coeFn {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : signedWeightEvenSubspace hw heven) :
    ((((weightPositiveProjection hw heven) f : signedWeightEvenSubspace hw heven) :
        SignedWeightL2 w) : ℝ → ℂ) =ᵐ[signedWeightMeasure w]
      fun t => weightPositiveSymbol w t * ((f : SignedWeightL2 w) : ℝ → ℂ) t :=
  signedWeightEvenBoundedMul_coeFn hw heven _ _ _ _ f

def signedWeightIndefiniteForm (w : ℝ → ℝ) {hw : Measurable w}
    {heven : ∀ t, w (-t) = w t}
    (f g : signedWeightEvenSubspace hw heven) : ℂ :=
  ∫ t : ℝ, (w t : ℂ) *
    inner ℂ (((f : SignedWeightL2 w) : ℝ → ℂ) t)
      (((g : SignedWeightL2 w) : ℝ → ℂ) t) ∂volume

/-- The positive Hilbert inner product weighted by `|w|`, twisted by the sign symmetry, is
literally integration against the signed density `w`. -/
theorem inner_weightFundamentalSymmetry_eq_signedWeightIndefiniteForm
    {w : ℝ → ℝ} (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (f g : signedWeightEvenSubspace hw heven) :
    inner ℂ (weightFundamentalSymmetry hw heven f) g =
      signedWeightIndefiniteForm w f g := by
  change inner ℂ
      (((weightFundamentalSymmetry hw heven f : signedWeightEvenSubspace hw heven) :
        SignedWeightL2 w))
      ((g : signedWeightEvenSubspace hw heven) : SignedWeightL2 w) = _
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ t : ℝ, inner ℂ
        ((((weightFundamentalSymmetry hw heven f : signedWeightEvenSubspace hw heven) :
          SignedWeightL2 w) : ℝ → ℂ) t)
        (((g : SignedWeightL2 w) : ℝ → ℂ) t) ∂signedWeightMeasure w) =
        ∫ t : ℝ, weightFundamentalSymbol w t *
          inner ℂ (((f : SignedWeightL2 w) : ℝ → ℂ) t)
            (((g : SignedWeightL2 w) : ℝ → ℂ) t) ∂signedWeightMeasure w := by
      apply integral_congr_ae
      filter_upwards [weightFundamentalSymmetry_coeFn hw heven f] with t hJ
      rw [hJ]
      by_cases hn : w t < 0 <;> simp [weightFundamentalSymbol, hn]
    _ = signedWeightIndefiniteForm w f g := by
      change (∫ t : ℝ, weightFundamentalSymbol w t *
          inner ℂ (((f : SignedWeightL2 w) : ℝ → ℂ) t)
            (((g : SignedWeightL2 w) : ℝ → ℂ) t)
          ∂volume.withDensity (realDensity fun t => |w t|)) = _
      rw [integral_withDensity_eq_integral_toReal_smul₀
          (measurable_signedWeightDensity hw).aemeasurable
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      unfold signedWeightIndefiniteForm
      apply integral_congr_ae
      filter_upwards with t
      have hdensity : (realDensity (fun u => |w u|) t).toReal = |w t| := by
        simp [realDensity]
      rw [hdensity]
      by_cases hn : w t < 0
      · rw [abs_of_neg hn]
        simp [weightFundamentalSymbol, hn]
      · have hnonneg : 0 ≤ w t := le_of_not_gt hn
        rw [abs_of_nonneg hnonneg]
        simp [weightFundamentalSymbol, hn]

def weightNegativeSector {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    Submodule ℂ (signedWeightEvenSubspace hw heven) :=
  LinearMap.range (weightNegativeProjection hw heven).toLinearMap

def weightPositiveSector {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    Submodule ℂ (signedWeightEvenSubspace hw heven) :=
  LinearMap.range (weightPositiveProjection hw heven).toLinearMap

theorem weightNegativeProjection_idempotent {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) : IsIdempotentElem (weightNegativeProjection hw heven) := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro f
  change weightNegativeProjection hw heven (weightNegativeProjection hw heven f) =
    weightNegativeProjection hw heven f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [weightNegativeProjection_coeFn hw heven f,
    weightNegativeProjection_coeFn hw heven (weightNegativeProjection hw heven f)]
      with t h1 h2
  rw [h2, h1]
  simp only [weightNegativeSymbol]
  split <;> simp

theorem weightPositiveProjection_idempotent {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) : IsIdempotentElem (weightPositiveProjection hw heven) := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro f
  change weightPositiveProjection hw heven (weightPositiveProjection hw heven f) =
    weightPositiveProjection hw heven f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [weightPositiveProjection_coeFn hw heven f,
    weightPositiveProjection_coeFn hw heven (weightPositiveProjection hw heven f)]
      with t h1 h2
  rw [h2, h1]
  simp only [weightPositiveSymbol]
  split <;> simp

theorem weightNegativeProjection_symmetric {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    (weightNegativeProjection hw heven).toLinearMap.IsSymmetric := by
  intro f g
  change inner ℂ
      (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w)
        (measurable_weightNegativeSymbol hw) (by norm_num)
        (norm_weightNegativeSymbol_le w) (f : SignedWeightL2 w))
      (g : SignedWeightL2 w) =
    inner ℂ (f : SignedWeightL2 w)
      (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w)
        (measurable_weightNegativeSymbol hw) (by norm_num)
        (norm_weightNegativeSymbol_le w) (g : SignedWeightL2 w))
  exact lpBoundedMulCLM_inner_real (measurable_weightNegativeSymbol hw) (by norm_num)
    (norm_weightNegativeSymbol_le w) (fun t => by simp [weightNegativeSymbol]) _ _

theorem weightPositiveProjection_symmetric {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    (weightPositiveProjection hw heven).toLinearMap.IsSymmetric := by
  intro f g
  change inner ℂ
      (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w)
        (measurable_weightPositiveSymbol hw) (by norm_num)
        (norm_weightPositiveSymbol_le w) (f : SignedWeightL2 w))
      (g : SignedWeightL2 w) =
    inner ℂ (f : SignedWeightL2 w)
      (lpBoundedMulCLM (p := 2) (μ := signedWeightMeasure w)
        (measurable_weightPositiveSymbol hw) (by norm_num)
        (norm_weightPositiveSymbol_le w) (g : SignedWeightL2 w))
  exact lpBoundedMulCLM_inner_real (measurable_weightPositiveSymbol hw) (by norm_num)
    (norm_weightPositiveSymbol_le w) (fun t => by simp [weightPositiveSymbol]) _ _

theorem weightNegativeProjection_isStarProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) : IsStarProjection (weightNegativeProjection hw heven) := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (weightNegativeProjection_idempotent hw heven),
    weightNegativeProjection_symmetric hw heven⟩

theorem weightPositiveProjection_isStarProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) : IsStarProjection (weightPositiveProjection hw heven) := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (weightPositiveProjection_idempotent hw heven),
    weightPositiveProjection_symmetric hw heven⟩

instance weightNegativeSector_hasOrthogonalProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    (weightNegativeSector hw heven).HasOrthogonalProjection :=
  (ContinuousLinearMap.IsStarProjection.isSymmetricProjection
    (weightNegativeProjection_isStarProjection hw heven)).hasOrthogonalProjection_range

instance weightPositiveSector_hasOrthogonalProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    (weightPositiveSector hw heven).HasOrthogonalProjection :=
  (ContinuousLinearMap.IsStarProjection.isSymmetricProjection
    (weightPositiveProjection_isStarProjection hw heven)).hasOrthogonalProjection_range

theorem weightNegativeProjection_eq_starProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    weightNegativeProjection hw heven = (weightNegativeSector hw heven).starProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp
    (weightNegativeProjection_isStarProjection hw heven)).2

theorem weightPositiveProjection_eq_starProjection {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    weightPositiveProjection hw heven = (weightPositiveSector hw heven).starProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp
    (weightPositiveProjection_isStarProjection hw heven)).2

theorem isClosed_weightNegativeSector {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    IsClosed (weightNegativeSector hw heven : Set (signedWeightEvenSubspace hw heven)) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (weightNegativeProjection_idempotent hw heven)

theorem isClosed_weightPositiveSector {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    IsClosed (weightPositiveSector hw heven : Set (signedWeightEvenSubspace hw heven)) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (weightPositiveProjection_idempotent hw heven)

theorem weightFundamentalSymmetry_negative {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : signedWeightEvenSubspace hw heven)
    (hf : f ∈ weightNegativeSector hw heven) :
    weightFundamentalSymmetry hw heven f = -f := by
  obtain ⟨g, rfl⟩ := hf
  change weightFundamentalSymmetry hw heven (weightNegativeProjection hw heven g) =
    -(weightNegativeProjection hw heven g)
  apply Subtype.ext
  change (((weightFundamentalSymmetry hw heven (weightNegativeProjection hw heven g) :
      signedWeightEvenSubspace hw heven) : SignedWeightL2 w)) =
    -(((weightNegativeProjection hw heven g : signedWeightEvenSubspace hw heven) :
      SignedWeightL2 w))
  apply Lp.ext
  filter_upwards [weightNegativeProjection_coeFn hw heven g,
    weightFundamentalSymmetry_coeFn hw heven (weightNegativeProjection hw heven g),
    Lp.coeFn_neg
      (((weightNegativeProjection hw heven g : signedWeightEvenSubspace hw heven) :
        SignedWeightL2 w))] with t hp hJ hneg
  rw [hJ, hneg]
  by_cases hn : w t < 0
  · simp [weightFundamentalSymbol, hn]
  · have hz : weightNegativeSymbol w t * ((g : SignedWeightL2 w) : ℝ → ℂ) t = 0 := by
      simp [weightNegativeSymbol, hn]
    have hpzero := hp.trans hz
    rw [hpzero]
    simp [weightFundamentalSymbol, hn]
    exact hpzero

theorem weightFundamentalSymmetry_positive {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) (f : signedWeightEvenSubspace hw heven)
    (hf : f ∈ weightPositiveSector hw heven) :
    weightFundamentalSymmetry hw heven f = f := by
  obtain ⟨g, rfl⟩ := hf
  change weightFundamentalSymmetry hw heven (weightPositiveProjection hw heven g) =
    weightPositiveProjection hw heven g
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [weightPositiveProjection_coeFn hw heven g,
    weightFundamentalSymmetry_coeFn hw heven (weightPositiveProjection hw heven g)]
      with t hp hJ
  rw [hJ, hp]
  simp only [weightFundamentalSymbol, weightPositiveSymbol]
  by_cases hn : w t < 0
  · have hp' : ¬ 0 < w t := by linarith
    simp [hn, hp']
  · by_cases hp' : 0 < w t <;> simp [hn, hp']

def normalizedIndicatorMeasure (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : μ s ≠ ∞) : Lp ℂ 2 μ :=
  ((Real.sqrt (μ.real s))⁻¹ : ℂ) • indicatorConstLp 2 hs hfin (1 : ℂ)

theorem normalizedIndicatorMeasure_ae (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : μ s ≠ ∞) :
    normalizedIndicatorMeasure μ s hs hfin =ᵐ[μ]
      fun x : ℝ => ((Real.sqrt (μ.real s))⁻¹ : ℂ) * s.indicator (fun _ => (1 : ℂ)) x := by
  change (((Real.sqrt (μ.real s))⁻¹ : ℂ) • indicatorConstLp 2 hs hfin (1 : ℂ) : Lp ℂ 2 μ)
    =ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (μ.real s))⁻¹ : ℂ)
      (indicatorConstLp 2 hs hfin (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (s := s) (hs := hs)
      (hμs := hfin) (c := (1 : ℂ))] with x hsmul hind
  rw [hsmul]
  change ((Real.sqrt (μ.real s))⁻¹ : ℂ) * indicatorConstLp 2 hs hfin (1 : ℂ) x = _
  rw [hind]

theorem norm_normalizedIndicatorMeasure (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : μ s ≠ ∞) (hpos : 0 < μ.real s) :
    ‖normalizedIndicatorMeasure μ s hs hfin‖ = 1 := by
  simp only [normalizedIndicatorMeasure, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_indicatorConstLp (p := 2) (μ := μ) (by norm_num) (by norm_num)]
  norm_num
  rw [show (μ.real s) ^ (1 / (2 : ℝ)) = Real.sqrt (μ.real s) by
    rw [Real.sqrt_eq_rpow]]
  rw [inv_mul_cancel₀]
  exact Real.sqrt_ne_zero'.mpr hpos

theorem inner_normalizedIndicatorMeasure_eq_zero (μ : Measure ℝ) {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ s ≠ ∞) (hft : μ t ≠ ∞) (hst : Disjoint s t) :
    inner ℂ (normalizedIndicatorMeasure μ s hs hfs)
      (normalizedIndicatorMeasure μ t ht hft) = 0 := by
  simp only [normalizedIndicatorMeasure, inner_smul_left, inner_smul_right]
  rw [MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one hs ht hfs hft]
  rw [hst.inter_eq, measureReal_empty]
  simp

theorem orthonormal_normalizedIndicatorMeasure (μ : Measure ℝ) {ι : Type*} {s : ι → Set ℝ}
    (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, μ (s i) ≠ ∞)
    (hpos : ∀ i, 0 < μ.real (s i)) (hdisj : Set.PairwiseDisjoint Set.univ s) :
    Orthonormal ℂ (fun i => normalizedIndicatorMeasure μ (s i) (hs i) (hfin i)) := by
  constructor
  · intro i
    exact norm_normalizedIndicatorMeasure μ (s i) (hs i) (hfin i) (hpos i)
  · intro i j hij
    exact inner_normalizedIndicatorMeasure_eq_zero μ (hs i) (hs j) (hfin i) (hfin j)
      (hdisj (Set.mem_univ i) (Set.mem_univ j) hij)

theorem signedWeightMeasure_evenShellCell_ne_top {w : ℝ → ℝ} (hw : Continuous w)
    {a b : ℝ} (hab : a < b) (n : ℕ) :
    signedWeightMeasure w (RHTower.evenShellCell a b n) ≠ ∞ := by
  have hmeas := RHTower.measurableSet_evenShellCell a b n
  have hsub := RHTower.evenShellCell_subset_Icc hab n
  obtain ⟨C, hC⟩ := (isCompact_Icc.bddAbove_image hw.abs.continuousOn)
  rw [signedWeightMeasure, withDensity_apply _ hmeas]
  have hle :
      (∫⁻ t in RHTower.evenShellCell a b n, realDensity (fun u => |w u|) t ∂volume) ≤
        ∫⁻ _t in RHTower.evenShellCell a b n, ENNReal.ofReal C ∂volume := by
    exact setLIntegral_mono' hmeas fun t ht =>
      ENNReal.ofReal_le_ofReal (hC ⟨t, hsub ht, rfl⟩)
  have hright :
      (∫⁻ _t in RHTower.evenShellCell a b n, ENNReal.ofReal C ∂volume) ≠ ∞ := by
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (RHTower.evenShellCell_measure_ne_top hab n)
  exact ne_top_of_le_ne_top hright hle

theorem signedWeightMeasure_evenShellCell_ne_zero {w : ℝ → ℝ} (hw : Measurable w)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ)
    (hnz : ∀ t ∈ RHTower.evenShellCell a b n, w t ≠ 0) :
    signedWeightMeasure w (RHTower.evenShellCell a b n) ≠ 0 := by
  rw [signedWeightMeasure, ne_eq,
    withDensity_apply_eq_zero (measurable_signedWeightDensity hw)]
  intro hzero
  have hsub : RHTower.evenShellCell a b n ⊆
      {t | realDensity (fun u => |w u|) t ≠ 0} ∩ RHTower.evenShellCell a b n := by
    intro t ht
    refine ⟨?_, ht⟩
    simpa [realDensity] using hnz t ht
  have hvolzero : volume (RHTower.evenShellCell a b n) = 0 :=
    measure_mono_null hsub hzero
  have hpos := RHTower.evenShellCell_measureReal_pos ha hab n
  have hrealzero : volume.real (RHTower.evenShellCell a b n) = 0 := by
    simp [Measure.real, hvolzero]
  rw [hrealzero] at hpos
  exact lt_irrefl 0 hpos

theorem signedWeightMeasure_evenShellCell_measureReal_pos {w : ℝ → ℝ} (hw : Continuous w)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ)
    (hnz : ∀ t ∈ RHTower.evenShellCell a b n, w t ≠ 0) :
    0 < (signedWeightMeasure w).real (RHTower.evenShellCell a b n) := by
  have hfin := signedWeightMeasure_evenShellCell_ne_top hw hab n
  have hne := signedWeightMeasure_evenShellCell_ne_zero hw.measurable ha hab n hnz
  exact lt_of_le_of_ne measureReal_nonneg ((measureReal_ne_zero_iff hfin).mpr hne).symm

theorem evenWeight_abs {w : ℝ → ℝ} (heven : ∀ t, w (-t) = w t) (t : ℝ) :
    w |t| = w t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), heven]

theorem evenShellCell_abs_mem_Icc {a b t : ℝ} (hab : a < b) {n : ℕ}
    (ht : t ∈ RHTower.evenShellCell a b n) : |t| ∈ Set.Icc a b := by
  change |t| ∈ RHTower.shellCell a b n at ht
  exact ⟨(RHTower.lt_shellLeft hab n).le.trans ht.1.le,
    ht.2.trans (RHTower.shellRight_lt hab n).le⟩

def signedWeightEvenShellVector (w : ℝ → ℝ) (hw : Continuous w)
    (a b : ℝ) (hab : a < b) (n : ℕ) : SignedWeightL2 w :=
  normalizedIndicatorMeasure (signedWeightMeasure w) (RHTower.evenShellCell a b n)
    (RHTower.measurableSet_evenShellCell a b n)
    (signedWeightMeasure_evenShellCell_ne_top hw hab n)

theorem signedWeightEvenShellVector_orthonormal {w : ℝ → ℝ} (hw : Continuous w)
    (heven : ∀ t, w (-t) = w t) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hnz : ∀ t ∈ Set.Icc a b, w t ≠ 0) :
    Orthonormal ℂ (signedWeightEvenShellVector w hw a b hab) := by
  exact orthonormal_normalizedIndicatorMeasure (signedWeightMeasure w)
    (RHTower.measurableSet_evenShellCell a b)
    (signedWeightMeasure_evenShellCell_ne_top hw hab)
    (fun n => signedWeightMeasure_evenShellCell_measureReal_pos hw ha hab n fun t ht => by
      rw [← evenWeight_abs heven]
      exact hnz |t| (evenShellCell_abs_mem_Icc hab ht))
    (RHTower.evenShellCell_pairwiseDisjoint hab)

theorem signedWeightReflection_evenShellVector {w : ℝ → ℝ} (hw : Continuous w)
    (heven : ∀ t, w (-t) = w t) (a b : ℝ) (hab : a < b) (n : ℕ) :
    signedWeightReflection hw.measurable heven (signedWeightEvenShellVector w hw a b hab n) =
      signedWeightEvenShellVector w hw a b hab n := by
  apply Lp.ext
  let s := RHTower.evenShellCell a b n
  let hs := RHTower.measurableSet_evenShellCell a b n
  let hfin := signedWeightMeasure_evenShellCell_ne_top hw hab n
  have hneg := (normalizedIndicatorMeasure_ae (signedWeightMeasure w) s hs hfin).comp_tendsto
    (measurePreserving_neg_signedWeightMeasure hw.measurable heven).quasiMeasurePreserving.tendsto_ae
  filter_upwards [signedWeightReflection_ae hw.measurable heven
      (signedWeightEvenShellVector w hw a b hab n), hneg,
    normalizedIndicatorMeasure_ae (signedWeightMeasure w) s hs hfin] with t href hnegx hx
  rw [href]
  change normalizedIndicatorMeasure (signedWeightMeasure w) s hs hfin (-t) =
    normalizedIndicatorMeasure (signedWeightMeasure w) s hs hfin t
  have hnegx' : normalizedIndicatorMeasure (signedWeightMeasure w) s hs hfin (-t) =
      ((Real.sqrt ((signedWeightMeasure w).real s))⁻¹ : ℂ) *
        s.indicator (fun _ => (1 : ℂ)) (-t) := by
    simpa [Function.comp_apply] using hnegx
  rw [hnegx', hx]
  have hmem : -t ∈ s ↔ t ∈ s := by simp [s, RHTower.evenShellCell]
  by_cases hts : t ∈ s
  · rw [Set.indicator_of_mem hts, Set.indicator_of_mem (hmem.mpr hts)]
  · rw [Set.indicator_of_notMem hts, Set.indicator_of_notMem (mt hmem.mp hts)]

def signedWeightEvenShellVectorEven {w : ℝ → ℝ} (hw : Continuous w)
    (heven : ∀ t, w (-t) = w t) (a b : ℝ) (hab : a < b) (n : ℕ) :
    signedWeightEvenSubspace hw.measurable heven :=
  ⟨signedWeightEvenShellVector w hw a b hab n,
    (mem_signedWeightEvenSubspace_iff hw.measurable heven _).mpr
      (signedWeightReflection_evenShellVector hw heven a b hab n)⟩

theorem signedWeightEvenShellVectorEven_orthonormal {w : ℝ → ℝ} (hw : Continuous w)
    (heven : ∀ t, w (-t) = w t) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hnz : ∀ t ∈ Set.Icc a b, w t ≠ 0) :
    Orthonormal ℂ (signedWeightEvenShellVectorEven hw heven a b hab) :=
  (signedWeightEvenShellVector_orthonormal hw heven a b ha hab hnz).codRestrict
    (signedWeightEvenSubspace hw.measurable heven)
    (fun n => (signedWeightEvenShellVectorEven hw heven a b hab n).property)

theorem signedWeightEvenShellVectorEven_mem_negativeSector {w : ℝ → ℝ} (hw : Continuous w)
    (heven : ∀ t, w (-t) = w t) {a b : ℝ} (hab : a < b)
    (hneg : ∀ t ∈ Set.Icc a b, w t < 0) (n : ℕ) :
    signedWeightEvenShellVectorEven hw heven a b hab n ∈
      weightNegativeSector hw.measurable heven := by
  let v := signedWeightEvenShellVectorEven hw heven a b hab n
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change (((weightNegativeProjection hw.measurable heven v :
      signedWeightEvenSubspace hw.measurable heven) : SignedWeightL2 w)) =
    ((v : signedWeightEvenSubspace hw.measurable heven) : SignedWeightL2 w)
  apply Lp.ext
  let s := RHTower.evenShellCell a b n
  let hs := RHTower.measurableSet_evenShellCell a b n
  let hfin := signedWeightMeasure_evenShellCell_ne_top hw hab n
  filter_upwards [weightNegativeProjection_coeFn hw.measurable heven v,
    normalizedIndicatorMeasure_ae (signedWeightMeasure w) s hs hfin] with t hp hv
  rw [hp]
  change weightNegativeSymbol w t *
      normalizedIndicatorMeasure (signedWeightMeasure w) s hs hfin t =
    normalizedIndicatorMeasure (signedWeightMeasure w) s hs hfin t
  rw [hv]
  by_cases ht : t ∈ s
  · have hwt : w t < 0 := by
      rw [← evenWeight_abs heven]
      exact hneg |t| (evenShellCell_abs_mem_Icc hab ht)
    simp [weightNegativeSymbol, hwt, ht]
  · simp [weightNegativeSymbol, ht]

theorem signedWeightEvenShellVectorEven_mem_positiveSector {w : ℝ → ℝ} (hw : Continuous w)
    (heven : ∀ t, w (-t) = w t) {a b : ℝ} (hab : a < b)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < w t) (n : ℕ) :
    signedWeightEvenShellVectorEven hw heven a b hab n ∈
      weightPositiveSector hw.measurable heven := by
  let v := signedWeightEvenShellVectorEven hw heven a b hab n
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change (((weightPositiveProjection hw.measurable heven v :
      signedWeightEvenSubspace hw.measurable heven) : SignedWeightL2 w)) =
    ((v : signedWeightEvenSubspace hw.measurable heven) : SignedWeightL2 w)
  apply Lp.ext
  let s := RHTower.evenShellCell a b n
  let hs := RHTower.measurableSet_evenShellCell a b n
  let hfin := signedWeightMeasure_evenShellCell_ne_top hw hab n
  filter_upwards [weightPositiveProjection_coeFn hw.measurable heven v,
    normalizedIndicatorMeasure_ae (signedWeightMeasure w) s hs hfin] with t hp hv
  rw [hp]
  change weightPositiveSymbol w t *
      normalizedIndicatorMeasure (signedWeightMeasure w) s hs hfin t =
    normalizedIndicatorMeasure (signedWeightMeasure w) s hs hfin t
  rw [hv]
  by_cases ht : t ∈ s
  · have hwt : 0 < w t := by
      rw [← evenWeight_abs heven]
      exact hpos |t| (evenShellCell_abs_mem_Icc hab ht)
    simp [weightPositiveSymbol, hwt, ht]
  · simp [weightPositiveSymbol, ht]

theorem exists_positive_Icc_of_continuous_of_pos {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 < t) (hwt : 0 < w t) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ x ∈ Set.Icc a b, 0 < w x := by
  have hopen : IsOpen {x : ℝ | 0 < w x} := isOpen_lt continuous_const hw
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t hwt
  let δ := min (ε / 2) (t / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (half_pos ht)
  have hδt : δ ≤ t / 2 := min_le_right _ _
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  refine ⟨t - δ, t + δ, by linarith, by linarith, ?_⟩
  intro x hx
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) hδε

theorem exists_negative_Icc_of_continuous_of_neg {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 < t) (hwt : w t < 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ x ∈ Set.Icc a b, w x < 0 := by
  obtain ⟨a, b, ha, hab, hpos⟩ :=
    exists_positive_Icc_of_continuous_of_pos hw.neg ht (neg_pos.mpr hwt)
  exact ⟨a, b, ha, hab, fun x hx => neg_pos.mp (hpos x hx)⟩

theorem weightNegativeSector_not_finiteDimensional_of_interval {w : ℝ → ℝ} (hw : Continuous w)
    (heven : ∀ t, w (-t) = w t) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hneg : ∀ t ∈ Set.Icc a b, w t < 0) :
    ¬ FiniteDimensional ℂ (weightNegativeSector hw.measurable heven) := by
  let v : ℕ → weightNegativeSector hw.measurable heven := fun n =>
    ⟨signedWeightEvenShellVectorEven hw heven a b hab n,
      signedWeightEvenShellVectorEven_mem_negativeSector hw heven hab hneg n⟩
  have hv : Orthonormal ℂ v :=
    (signedWeightEvenShellVectorEven_orthonormal hw heven a b ha hab
      (fun t ht => (hneg t ht).ne)).codRestrict
        (weightNegativeSector hw.measurable heven)
        (signedWeightEvenShellVectorEven_mem_negativeSector hw heven hab hneg)
  intro hfd
  letI : FiniteDimensional ℂ (weightNegativeSector hw.measurable heven) := hfd
  exact Module.Finite.not_linearIndependent_of_infinite v hv.linearIndependent

theorem weightPositiveSector_not_finiteDimensional_of_interval {w : ℝ → ℝ} (hw : Continuous w)
    (heven : ∀ t, w (-t) = w t) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < w t) :
    ¬ FiniteDimensional ℂ (weightPositiveSector hw.measurable heven) := by
  let v : ℕ → weightPositiveSector hw.measurable heven := fun n =>
    ⟨signedWeightEvenShellVectorEven hw heven a b hab n,
      signedWeightEvenShellVectorEven_mem_positiveSector hw heven hab hpos n⟩
  have hv : Orthonormal ℂ v :=
    (signedWeightEvenShellVectorEven_orthonormal hw heven a b ha hab
      (fun t ht => (hpos t ht).ne')).codRestrict
        (weightPositiveSector hw.measurable heven)
        (signedWeightEvenShellVectorEven_mem_positiveSector hw heven hab hpos)
  intro hfd
  letI : FiniteDimensional ℂ (weightPositiveSector hw.measurable heven) := hfd
  exact Module.Finite.not_linearIndependent_of_infinite v hv.linearIndependent

end GaloisForLFunctions.HTGeometry
