import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.ConvolutionSmoothing
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.ContinuousKernelOperators

/-!
# Compactness of smoothing on a fixed compact support

Continuous kernel sections over the compact input support form an `L²` field
of functionals on the compact output support. The corpus kernel theorem gives
a compact operator. Extension by zero identifies it with actual convolution.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology Convolution Pointwise
namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev.L2Compactness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance compactConvolutionMeasurableSpace : MeasurableSpace E := borel E
local instance compactConvolutionBorelSpace : BorelSpace E := ⟨rfl⟩

lemma compactSubtype_volume_finite (K : Set E) (hK : IsCompact K) :
    IsFiniteMeasure ((volume : Measure E).comap (Subtype.val : K → E)) := by
  constructor
  have hm := (measurePreserving_subtype_coe (μa := (volume : Measure E)) hK.measurableSet).measure_preimage
    MeasurableSet.univ.nullMeasurableSet
  have he : ((volume : Measure E).comap (Subtype.val : K → E)) univ=volume K := by
    simpa only [preimage_univ,Measure.restrict_apply_univ] using hm
  exact he.trans_lt hK.measure_lt_top

/-- Convolution kernel restricted to the compact input support. -/
def convolutionSectionKernel (K : Set E) (ψ : E → ℝ) (hc : Continuous ψ) : C(E × K,ℝ) where
  toFun p := ψ (p.1-p.2)
  continuous_toFun := hc.comp (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))

/-- Compact output restriction of the kernel operator, extended by zero. -/
def compactSmoothingOperator (K : Set E) (hK : IsCompact K)
    (ψ : E → ℝ) (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    Lp ℝ 2 (volume.restrict K) →L[ℝ] Lp ℝ 2 (volume : Measure E) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI := compactSubtype_volume_finite K hK
  exact (LpExtension.extendIsometry (μ := (volume : Measure E)) (E := ℝ) (p := (2:ℝ≥0∞)) (hK.add hs).measurableSet).toContinuousLinearMap.comp
    ((compactOutputKernelOperator (volume : Measure E)
      ((volume : Measure E).comap (Subtype.val : K → E))
      (K+tsupport ψ) (hK.add hs) (convolutionSectionKernel K ψ hc)).comp
      (Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℝ) (p := (2:ℝ≥0∞)) (f := (Subtype.val : K → E))
        (measurePreserving_subtype_coe (μa := (volume : Measure E)) hK.measurableSet)).toContinuousLinearMap)

theorem compactSmoothingOperator_compact (K : Set E) (hK : IsCompact K)
    (ψ : E → ℝ) (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    IsCompactOperator (compactSmoothingOperator K hK ψ hc hs) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI := compactSubtype_volume_finite K hK
  exact ((compactOutputKernelOperator_compact (volume : Measure E)
    ((volume : Measure E).comap (Subtype.val : K → E))
    (K+tsupport ψ) (hK.add hs) (convolutionSectionKernel K ψ hc)).comp_clm
      (Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℝ) (p := (2:ℝ≥0∞)) (f := (Subtype.val : K → E))
        (measurePreserving_subtype_coe (μa := (volume : Measure E)) hK.measurableSet)).toContinuousLinearMap).clm_comp
      (LpExtension.extendIsometry (μ := (volume : Measure E)) (E := ℝ) (p := (2:ℝ≥0∞)) (hK.add hs).measurableSet).toContinuousLinearMap

lemma smoothFun_eq_subtype_integral (K : Set E) (hKm : MeasurableSet K)
    (ψ : E → ℝ) (u : Lp ℝ 2 (volume.restrict K)) (x : E) :
    smoothFun ψ u x=∫y : K,ψ (x-y)*u y ∂(volume : Measure E).comap Subtype.val := by
  change (∫y,(K.indicator u) y*ψ (x-y) ∂(volume : Measure E))=_
  calc
    _=∫y,K.indicator (fun y=>ψ (x-y)*u y) y ∂(volume : Measure E) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y=>by
        by_cases hy : y∈K <;> simp [hy,mul_comm])
    _=∫y in K,ψ (x-y)*u y ∂(volume : Measure E) := integral_indicator hKm
    _=_ := (integral_subtype_comap hKm (fun y=>ψ (x-y)*u y)).symm

/-- The functional-field construction agrees with the actual convolution class. -/
lemma compactSmoothingOperator_eq_smoothL2 (K : Set E) (hK : IsCompact K)
    (ψ : E → ℝ) (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    (u : Lp ℝ 2 (volume.restrict K)) :
    compactSmoothingOperator K hK ψ hc hs u=smoothL2 ψ hK hK.measurableSet hc hs u := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI := compactSubtype_volume_finite K hK
  let ν : Measure K := (volume : Measure E).comap Subtype.val
  let r := Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℝ) (p := (2:ℝ≥0∞)) (f := (Subtype.val : K → E))
    (measurePreserving_subtype_coe (μa := (volume : Measure E)) hK.measurableSet)
  let S := K+tsupport ψ
  let T := compactOutputKernelOperator (volume : Measure E) ν S (hK.add hs)
    (convolutionSectionKernel K ψ hc)
  have hr : (r u : K → ℝ) =ᵐ[ν] fun y=>u y := Lp.coeFn_compMeasurePreserving u _
  have hT : (T (r u) : E → ℝ) =ᵐ[volume.restrict S] smoothFun ψ u := by
    filter_upwards [compactOutputKernelOperator_coe (volume : Measure E) ν S (hK.add hs)
      (convolutionSectionKernel K ψ hc) (r u)] with x hx
    rw [hx,smoothFun_eq_subtype_integral K hK.measurableSet]
    apply integral_congr_ae
    filter_upwards [hr] with y hy
    exact congrArg (fun t=>ψ (x-y)*t) hy
  apply Lp.ext
  filter_upwards [LpExtension.extendIsometry_coe (hK.add hs).measurableSet (T (r u)),
    (ae_restrict_iff' (hK.add hs).measurableSet).mp hT,
    smoothL2_ae_eq (K := K) (ψ := ψ) hK hK.measurableSet hc hs u] with x he ht hf
  change (LpExtension.extendIsometry (hK.add hs).measurableSet (T (r u))) x=_
  rw [he,hf]
  by_cases hx : x∈S
  · rw [Set.indicator_of_mem hx,ht hx]
  · rw [Set.indicator_of_notMem hx]
    symm
    by_contra hz
    exact hx (support_smoothFun_subset_add_tsupport ψ u hz)

/-- Smoothing sends every bounded ball to a relatively compact family. -/
theorem smoothL2_image_closedBall_isCompact (K : Set E) (hK : IsCompact K)
    (ψ : E → ℝ) (hc : Continuous ψ) (hs : HasCompactSupport ψ) (R : ℝ) :
    IsCompact (closure (smoothL2 ψ hK hK.measurableSet hc hs '' Metric.closedBall (0 : _) R)) := by
  have he : smoothL2 ψ hK hK.measurableSet hc hs=compactSmoothingOperator K hK ψ hc hs :=
    funext (fun u=>(compactSmoothingOperator_eq_smoothL2 K hK ψ hc hs u).symm)
  rw [he]
  exact (compactSmoothingOperator_compact K hK ψ hc hs).isCompact_closure_image_closedBall R

#print axioms compactSmoothingOperator_eq_smoothL2
#print axioms smoothL2_image_closedBall_isCompact
end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev.L2Compactness
