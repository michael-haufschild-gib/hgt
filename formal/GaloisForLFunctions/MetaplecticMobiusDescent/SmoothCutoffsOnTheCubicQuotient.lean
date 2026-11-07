/-
Smooth cutoffs and chart measure transport adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicQuotientHasLocalMeasureCharts
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth cutoffs on the cubic quotient

Positive-height Euclidean coordinates identify injective quotient charts.
Every quotient point admits a compactly supported smooth cutoff equal to one
at a lift. Restricted hyperbolic volume maps exactly to restricted quotient
volume on its support, giving local integral identities and bounds.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

abbrev KernelQuotient := IntegralOrbitQuotient globalKubotaKernel

/-- Horizontal real and imaginary parts followed by positive height. -/
def hyperbolicEuclideanCoordinates (w : HyperbolicSpace) : EuclideanSpatial :=
  WithLp.toLp 2 ![(hyperbolicHorizontal w).re,(hyperbolicHorizontal w).im,hyperbolicHeight w]

lemma hyperbolicEuclideanCoordinates_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicEuclideanCoordinates (upperPoint z v hv)=WithLp.toLp 2 ![z.re,z.im,v] := by
  simp only [hyperbolicEuclideanCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]

lemma euclideanToHyperbolic_coordinates (w : HyperbolicSpace) :
    euclideanToHyperbolic (hyperbolicEuclideanCoordinates w)=w := by
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  rw [euclideanToHyperbolic_positive _ hp]
  change upperPoint (((hyperbolicHorizontal w).re:ℂ)+Complex.I*((hyperbolicHorizontal w).im:ℂ))
    (hyperbolicHeight w) hp=w
  rw [mul_comm Complex.I,Complex.re_add_im]
  exact upperCoordinates_right_inverse w

lemma hyperbolicEuclideanCoordinates_toHyperbolic (p : EuclideanSpatial) (hp : 0<p 2) :
    hyperbolicEuclideanCoordinates (euclideanToHyperbolic p)=p := by
  rw [euclideanToHyperbolic_positive _ hp,hyperbolicEuclideanCoordinates_upperPoint]
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j <;> simp

lemma hyperbolicEuclideanCoordinates_continuous : Continuous hyperbolicEuclideanCoordinates := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hyperbolicHorizontal_continuous
  · exact Complex.continuous_im.comp hyperbolicHorizontal_continuous
  · exact hyperbolicHeight_continuous

lemma euclideanToHyperbolic_continuousAt (p : EuclideanSpatial) (hp : 0<p 2) :
    ContinuousAt euclideanToHyperbolic p := by
  apply continuous_upperCoordinates.continuousAt.comp
  rw [ContinuousAt, tendsto_subtype_rng]
  apply ContinuousAt.prodMk
  · change ContinuousAt (fun q : EuclideanSpatial => (q 0:ℂ)+Complex.I*(q 1:ℂ)) p
    fun_prop
  · have he : positiveCoordinateHeight =ᶠ[𝓝 p] fun q : EuclideanSpatial => q 2 := by
      filter_upwards [(by fun_prop : Continuous (fun q : EuclideanSpatial => q 2)).continuousAt.eventually_const_lt hp] with q hq
      simp only [positiveCoordinateHeight,if_pos hq]
    exact (by fun_prop : ContinuousAt (fun q : EuclideanSpatial => q 2) p).congr_of_eventuallyEq he

/-- Smooth compactly supported cutoff contained in the upper half-space. -/
structure PositiveChartCutoff where
  func : EuclideanSpatial → ℝ
  smooth : ContDiff ℝ ∞ func
  compact : HasCompactSupport func
  positive : tsupport func ⊆ {p | 0 < p 2}

/-- A bump supported inside a locally injective chart around any positive-height point. -/
lemma kernelChartCutoff_exists (p : EuclideanSpatial) (hp : 0<p 2) :
    ∃χ : PositiveChartCutoff, χ.func p=1 ∧ Set.range χ.func ⊆ Set.Icc 0 1 ∧
      Set.InjOn (integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic)
        (tsupport χ.func) := by
  obtain ⟨U,hU,hw,hUinj⟩ :=
    kernelQuotient_localHomeomorph.isLocallyInjective (euclideanToHyperbolic p)
  have hn : {q : EuclideanSpatial | 0<q 2} ∩ euclideanToHyperbolic ⁻¹' U ∈ 𝓝 p :=
    inter_mem ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hp)
      (euclideanToHyperbolic_continuousAt p hp (hU.mem_nhds hw))
  obtain ⟨χ,hχ,hcomp,hsmooth,hrange,hvalue⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hn
  refine ⟨⟨χ,hsmooth,hcomp,fun q hq => (hχ hq).1⟩,hvalue,hrange,?_⟩
  intro q hq r hr heq
  have hwEq := hUinj (hχ hq).2 (hχ hr).2 heq
  have hc := congrArg hyperbolicEuclideanCoordinates hwEq
  simpa only [hyperbolicEuclideanCoordinates_toHyperbolic _ (hχ hq).1,
    hyperbolicEuclideanCoordinates_toHyperbolic _ (hχ hr).1] using hc

def kernelEuclideanProjection : EuclideanSpatial → KernelQuotient :=
  integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic

lemma kernelEuclideanProjection_measurable : Measurable kernelEuclideanProjection :=
  (measurable_integralOrbitProjection _).comp euclideanToHyperbolic_measurable

/-- Coordinate transport holds for every measurable set since volume ignores nonpositive height. -/
lemma euclideanToHyperbolic_measurePreserving_on (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) :
    MeasurePreserving euclideanToHyperbolic (hyperbolicEuclideanVolume.restrict S)
      (hyperbolicVolume.restrict (hyperbolicEuclideanCoordinates ⁻¹' S)) := by
  have hU : MeasurableSet (hyperbolicEuclideanCoordinates ⁻¹' S) :=
    hyperbolicEuclideanCoordinates_continuous.measurable hS
  have hset : euclideanToHyperbolic ⁻¹' (hyperbolicEuclideanCoordinates ⁻¹' S)=ᵐ[hyperbolicEuclideanVolume]S := by
    filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
    change (hyperbolicEuclideanCoordinates (euclideanToHyperbolic p) ∈ S) = (p ∈ S)
    rw [hyperbolicEuclideanCoordinates_toHyperbolic p hp]
  refine ⟨euclideanToHyperbolic_measurable,?_⟩
  rw [hyperbolicVolume,Measure.restrict_map euclideanToHyperbolic_measurable hU,
    Measure.restrict_congr_set hset]

lemma euclideanToHyperbolic_image_positive (S : Set EuclideanSpatial)
    (hpos : S⊆euclideanUpperHalf) :
    euclideanToHyperbolic '' S=hyperbolicEuclideanCoordinates ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa only [Set.mem_preimage,hyperbolicEuclideanCoordinates_toHyperbolic p (hpos hp)] using hp
  · intro hw
    exact ⟨hyperbolicEuclideanCoordinates w,hw,euclideanToHyperbolic_coordinates w⟩

lemma kernelEuclideanProjection_measurePreserving_on (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) :
    MeasurePreserving kernelEuclideanProjection (hyperbolicEuclideanVolume.restrict S)
      ((integralQuotientVolume globalKubotaKernel).restrict (kernelEuclideanProjection '' S)) := by
  have hU : MeasurableSet (hyperbolicEuclideanCoordinates ⁻¹' S) :=
    hyperbolicEuclideanCoordinates_continuous.measurable hS
  have hi : Set.InjOn (integralOrbitProjection globalKubotaKernel)
      (hyperbolicEuclideanCoordinates ⁻¹' S) := by
    intro u hu v hv heq
    have hh := hinj hu hv (by simpa only [kernelEuclideanProjection,Function.comp_apply,
      euclideanToHyperbolic_coordinates] using heq)
    have hh' := congrArg euclideanToHyperbolic hh
    simpa only [euclideanToHyperbolic_coordinates] using hh'
  have hcomp := (kernelProjection_measurePreserving_on _ hU hi).comp
    (euclideanToHyperbolic_measurePreserving_on S hS)
  have himage : integralOrbitProjection globalKubotaKernel ''
      (hyperbolicEuclideanCoordinates ⁻¹' S)=kernelEuclideanProjection '' S := by
    rw [←euclideanToHyperbolic_image_positive S hpos,Set.image_image]
    rfl
  rwa [himage] at hcomp

lemma kernelEuclideanProjection_integral (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := hg.mono_measure (Measure.restrict_le_self (s := kernelEuclideanProjection '' S))
  rw [←hm.map_eq] at hh ⊢
  exact (integral_map hm.measurable.aemeasurable hh).symm

lemma kernelEuclideanProjection_integral_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) (hgn : ∀q,0≤g q) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)≤
      ∫q,g q∂integralQuotientVolume globalKubotaKernel := by
  rw [kernelEuclideanProjection_integral S hS hpos hinj g hg.aestronglyMeasurable]
  exact setIntegral_le_integral hg (Eventually.of_forall hgn)


/-- Every quotient point has a smooth cutoff supported in a measure-preserving chart. -/
theorem kernelQuotient_chartCutoff_exists (q : KernelQuotient) :
    ∃ (p : EuclideanSpatial) (χ : PositiveChartCutoff),
      kernelEuclideanProjection p=q ∧ χ.func p=1 ∧
      Set.range χ.func ⊆ Set.Icc 0 1 ∧
      Set.InjOn kernelEuclideanProjection (tsupport χ.func) ∧
      MeasurePreserving kernelEuclideanProjection
        (hyperbolicEuclideanVolume.restrict (tsupport χ.func))
        ((integralQuotientVolume globalKubotaKernel).restrict
          (kernelEuclideanProjection '' tsupport χ.func)) := by
  obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
  obtain ⟨χ,hχ,hrange,hinj⟩ := kernelChartCutoff_exists
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
  refine ⟨hyperbolicEuclideanCoordinates w,χ,?_,hχ,hrange,hinj,?_⟩
  · change integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (hyperbolicEuclideanCoordinates w))=
        integralOrbitProjection globalKubotaKernel w
    rw [euclideanToHyperbolic_coordinates]
  · exact kernelEuclideanProjection_measurePreserving_on _
      (isClosed_tsupport χ.func).measurableSet χ.positive hinj

#print axioms kernelQuotient_chartCutoff_exists
#print axioms kernelEuclideanProjection_measurePreserving_on
#print axioms kernelEuclideanProjection_integral_le

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
