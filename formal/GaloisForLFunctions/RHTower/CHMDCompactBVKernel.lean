import GaloisForLFunctions.RHTower.CHMDCompactBVTranslations
import GaloisForLFunctions.RHTower.CHMDGraphMollification
import GaloisForLFunctions.HTGeometry.ContinuousKernelBochnerControl
import GaloisForLFunctions.HTGeometry.CompactIntervalConvolution

/-! # Compact integral kernels into the complete arithmetic graph

Continuous input on a compact interval acts on literal cutoff kernels by a
bounded linear map. Its source coordinate is the pointwise scalar integral.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal BoundedContinuousFunction Convolution

namespace RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry
attribute [local instance] Measure.Subtype.measureSpace

theorem finiteVolumeIcc (a : ℝ≥0) :
    IsFiniteMeasure (volume : Measure (Icc (0 : ℝ) (a : ℝ))) := by
  refine ⟨?_⟩
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top

attribute [local instance] finiteVolumeIcc

theorem bv_reflection {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) :
    BoundedVariationOn (fun x => f (-x)) univ := by
  simpa only [zero_sub] using bv_reflected_translate hf 0

def cutoffKernelGraph (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ) (b y : ℝ) :
    SourceGraph := cutoffTranslateGraph χ (fun z => ρ (-z)) hχ (bv_reflection hρ) (y - b)

def cutoffKernelBCF (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (b y : ℝ) : ℝ →ᵇ ℝ :=
  cutoffTranslateBCF χ (fun z => ρ (-z)) hχ (bv_reflection hρ)
    hcχ (hcρ.comp continuous_neg) (y - b)

theorem cutoffKernelBCF_apply (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (b y x : ℝ) :
    cutoffKernelBCF χ ρ hχ hρ hcχ hcρ b y x = χ x * ρ (x + b - y) := by
  change χ x * ρ (-(y - b - x)) = _
  congr 2
  ring

theorem continuous_cutoffKernelGraph (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (hsχ : HasCompactSupport χ) (b : ℝ) :
    Continuous (cutoffKernelGraph χ ρ hχ hρ b) :=
  (continuous_cutoffTranslateGraph χ (fun z => ρ (-z)) hχ (bv_reflection hρ)
    hcχ (hcρ.comp continuous_neg) hsχ).comp (continuous_id.sub continuous_const)

theorem continuous_cutoffKernelBCF (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (hsχ : HasCompactSupport χ) (b : ℝ) :
    Continuous (cutoffKernelBCF χ ρ hχ hρ hcχ hcρ b) :=
  (continuous_cutoffTranslateBCF χ (fun z => ρ (-z)) hχ (bv_reflection hρ)
    hcχ (hcρ.comp continuous_neg) hsχ).comp (continuous_id.sub continuous_const)

theorem cutoffKernelGraph_source_bcf (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (b y : ℝ) :
    sourceMap (cutoffKernelGraph χ ρ hχ hρ b y) =
      BoundedContinuousFunction.toLp 2 massMeasure ℝ
        (cutoffKernelBCF χ ρ hχ hρ hcχ hcρ b y) :=
  cutoffTranslateGraph_source_bcf _ _ _ _ _ _ _

def compactKernelControl (a : ℝ≥0) (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (hsχ : HasCompactSupport χ) (b : ℝ) :
    C(Icc (0 : ℝ) (a : ℝ), ℝ) →L[ℝ] SourceGraph :=
  continuousKernelBochnerControl volume (fun y => cutoffKernelGraph χ ρ hχ hρ b y)
    (ContinuousMap.memLp (μ := volume) (p := 1) ℝ
      ⟨_, (continuous_cutoffKernelGraph χ ρ hχ hρ hcχ hcρ hsχ b).comp continuous_subtype_val⟩)

theorem compactKernelControl_apply (a : ℝ≥0) (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (hsχ : HasCompactSupport χ) (b : ℝ)
    (f : C(Icc (0 : ℝ) (a : ℝ), ℝ)) :
    compactKernelControl a χ ρ hχ hρ hcχ hcρ hsχ b f =
      ∫ y : Icc (0 : ℝ) (a : ℝ), f y • cutoffKernelGraph χ ρ hχ hρ b y :=
  continuousKernelBochnerControl_apply _ _ _ _

theorem compactKernelControl_source (a : ℝ≥0) (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (hsχ : HasCompactSupport χ) (b : ℝ)
    (f : C(Icc (0 : ℝ) (a : ℝ), ℝ)) :
    sourceMap (compactKernelControl a χ ρ hχ hρ hcχ hcρ hsχ b f) =
      BoundedContinuousFunction.toLp 2 massMeasure ℝ
        (∫ y : Icc (0 : ℝ) (a : ℝ), f y • cutoffKernelBCF χ ρ hχ hρ hcχ hcρ b y) := by
  rw [compactKernelControl_apply]
  apply sourceMap_integral_boundedContinuous
  · exact memLp_one_iff_integrable.mp (ContinuousMap.memLp (μ := volume) (p := 1) ℝ
      ⟨_, f.continuous.smul ((continuous_cutoffKernelGraph χ ρ hχ hρ hcχ hcρ hsχ b).comp
        continuous_subtype_val)⟩)
  · exact memLp_one_iff_integrable.mp (ContinuousMap.memLp (μ := volume) (p := 1) ℝ
      ⟨_, f.continuous.smul ((continuous_cutoffKernelBCF χ ρ hχ hρ hcχ hcρ hsχ b).comp
        continuous_subtype_val)⟩)
  · exact Eventually.of_forall fun y => by
      rw [map_smul, map_smul, cutoffKernelGraph_source_bcf]

theorem compactKernelBCF_integral_apply (a : ℝ≥0) (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (hsχ : HasCompactSupport χ) (b : ℝ)
    (f : C(Icc (0 : ℝ) (a : ℝ), ℝ)) (x : ℝ) :
    (∫ y : Icc (0 : ℝ) (a : ℝ), f y • cutoffKernelBCF χ ρ hχ hρ hcχ hcρ b y) x =
      ∫ y : Icc (0 : ℝ) (a : ℝ), f y * (χ x * ρ (x + b - y)) := by
  have hi : Integrable (fun y : Icc (0 : ℝ) (a : ℝ) =>
      f y • cutoffKernelBCF χ ρ hχ hρ hcχ hcρ b y) :=
    memLp_one_iff_integrable.mp (ContinuousMap.memLp (μ := volume) (p := 1) ℝ
      ⟨_, f.continuous.smul ((continuous_cutoffKernelBCF χ ρ hχ hρ hcχ hcρ hsχ b).comp
        continuous_subtype_val)⟩)
  rw [boundedContinuous_integral_apply hi x]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change f y * cutoffKernelBCF χ ρ hχ hρ hcχ hcρ b y x = _
    rw [cutoffKernelBCF_apply]

theorem compactKernelControl_eq_average (a : ℝ≥0) (b : ℝ) (χ ρ F : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hF : BoundedVariationOn F univ) (hcχ : Continuous χ) (hcρ : Continuous ρ)
    (hcF : Continuous F) (hsχ : HasCompactSupport χ) (hsρ : HasCompactSupport ρ)
    (hfit : ∀ x y, y ∉ Icc (0 : ℝ) (a : ℝ) → χ x * ρ (x + b - y) = 0) :
    compactKernelControl a χ ρ hχ hρ hcχ hcρ hsχ b
        ⟨fun y => F y, hcF.comp continuous_subtype_val⟩ =
      ∫ s : ℝ, ρ s • cutoffKernelGraph χ F hχ hF b s := by
  have hp : Integrable (fun s : ℝ => ρ s • cutoffKernelGraph χ F hχ hF b s) := by
    have hc : Continuous (fun s : ℝ => ρ s • cutoffKernelGraph χ F hχ hF b s) :=
      hcρ.smul (continuous_cutoffKernelGraph χ F hχ hF hcχ hcF hsχ b)
    exact hc.integrable_of_hasCompactSupport hsρ.smul_right
  have hb : Integrable (fun s : ℝ => ρ s • cutoffKernelBCF χ F hχ hF hcχ hcF b s) := by
    have hc : Continuous (fun s : ℝ => ρ s • cutoffKernelBCF χ F hχ hF hcχ hcF b s) :=
      hcρ.smul (continuous_cutoffKernelBCF χ F hχ hF hcχ hcF hsχ b)
    exact hc.integrable_of_hasCompactSupport hsρ.smul_right
  apply source_projection_injective
  change sourceMap _ = sourceMap _
  rw [compactKernelControl_source,
    sourceMap_integral_boundedContinuous hp hb (Eventually.of_forall fun s => by
      rw [map_smul, map_smul, cutoffKernelGraph_source_bcf])]
  congr 1
  ext x
  rw [compactKernelBCF_integral_apply a χ ρ hχ hρ hcχ hcρ hsχ b _ x,
    boundedContinuous_integral_apply hb x]
  change (∫ y : Icc (0 : ℝ) (a : ℝ), F y * (χ x * ρ (x + b - y))) = _
  rw [cutoff_kernel_interval_eq_convolution a b χ ρ F hfit x]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    change ρ s * (χ x * F (x + b - s)) = ρ s * cutoffKernelBCF χ F hχ hF hcχ hcF b s x
    rw [cutoffKernelBCF_apply]

theorem cutoffKernelGraph_mollifier_tendsto (χ v : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hv : BoundedVariationOn v univ)
    (hcχ : Continuous χ) (hcv : Continuous v) (hsχ : HasCompactSupport χ) :
    Tendsto (fun n => ∫ s : ℝ, mollifier n s • cutoffKernelGraph χ v hχ hv 0 s)
      atTop (𝓝 (cutoffKernelGraph χ v hχ hv 0 0)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℝ))
    narrowBump_rOut_tendsto
    ((continuous_cutoffKernelGraph χ v hχ hv hcχ hcv hsχ 0).comp continuous_neg) 0
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg,
    neg_zero, mollifier, Function.comp_apply] using h

end RHTower.CHMDDoobGraph
