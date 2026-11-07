/-
Cubic cusp volume coordinates adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCuspAverages

/-!
# Horizontal and vertical integrals on the actual cusp strip

A measure-preserving coordinate split expresses hyperbolic cusp integrals
as horizontal period-domain integrals weighted by `v⁻³`. Compact height
and bounded fundamental domain make continuous weighted tests integrable.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def spatialComplexSplit : EuclideanSpatial ≃ᵐ ℝ × ℂ :=
  spatialHeightSplit.trans ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivPi.symm)

lemma spatialComplexSplit_fst (p : EuclideanSpatial) : (spatialComplexSplit p).1=p 2 := rfl
lemma spatialComplexSplit_snd (p : EuclideanSpatial) :
    (spatialComplexSplit p).2=(p 0:ℂ)+(p 1:ℂ)*Complex.I := rfl

lemma spatialComplexSplit_preserves_volume : MeasurePreserving spatialComplexSplit volume volume :=
  ((MeasurePreserving.id volume).prod Complex.volume_preserving_equiv_pi.symm).comp
    spatialHeightSplit_preserves_volume

lemma spatialComplexSplit_coordinates (w : HyperbolicSpace) :
    spatialComplexSplit (hyperbolicEuclideanCoordinates w)=
      (hyperbolicHeight w,hyperbolicHorizontal w) := by
  apply Prod.ext
  · rfl
  · change (hyperbolicHorizontal w).re+(hyperbolicHorizontal w).im*Complex.I=hyperbolicHorizontal w
    exact Complex.re_add_im _

def cuspCoordinateLift (q : ℝ × ℂ) : HyperbolicSpace :=
  euclideanToHyperbolic (spatialComplexSplit.symm q)

lemma cuspCoordinateLift_positive (v : ℝ) (z : ℂ) (hv : 0<v) :
    cuspCoordinateLift (v,z)=upperPoint z v hv := by
  have he : spatialComplexSplit (hyperbolicEuclideanCoordinates (upperPoint z v hv))=(v,z) := by
    simp only [spatialComplexSplit_coordinates,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  have he' := congrArg spatialComplexSplit.symm he
  rw [spatialComplexSplit.symm_apply_apply] at he'
  rw [cuspCoordinateLift,←he',euclideanToHyperbolic_coordinates]

def cuspEuclideanStrip : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Icc (5:ℝ) 6 ×ˢ periodDomain)

lemma cuspEuclideanStrip_measurable : MeasurableSet cuspEuclideanStrip :=
  spatialComplexSplit.measurable (measurableSet_Icc.prod periodDomain_measurable)

lemma cuspEuclideanStrip_positive : cuspEuclideanStrip⊆euclideanUpperHalf := by
  intro p hp
  have hh : 5≤p 2 := hp.1.1
  change 0<p 2
  linarith

lemma cuspEuclideanStrip_preimage :
    hyperbolicEuclideanCoordinates ⁻¹' cuspEuclideanStrip=cuspPeriodStrip 5 6 := by
  ext w
  change spatialComplexSplit (hyperbolicEuclideanCoordinates w)∈(Set.Icc (5:ℝ) 6 ×ˢ periodDomain) ↔ _
  rw [spatialComplexSplit_coordinates]
  exact and_comm

lemma cuspPeriodStrip_integral_coordinates (g : HyperbolicSpace→ℂ)
    (hg : AEStronglyMeasurable g hyperbolicVolume)
    (hint : IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume) :
    (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3 := by
  have hm := euclideanToHyperbolic_measurePreserving_on cuspEuclideanStrip
    cuspEuclideanStrip_measurable
  rw [cuspEuclideanStrip_preimage] at hm
  have hh := hg.mono_measure (Measure.restrict_le_self (s := cuspPeriodStrip 5 6))
  have he : (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
    rw [←hm.map_eq] at hh ⊢
    exact integral_map hm.measurable.aemeasurable hh
  rw [he,hyperbolicEuclidean_setIntegral_complex cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map
    (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
    (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : (∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)/(p 2:ℂ)^3)=
      ∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,g (cuspCoordinateLift q)/(q.1:ℂ)^3 := by
    rw [hsplit]
    simp only [cuspEuclideanStrip,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply,
      spatialComplexSplit_fst]
  rw [heq]
  change (∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,
    g (cuspCoordinateLift q)/(q.1:ℂ)^3 ∂((volume : Measure ℝ).prod volume))=_
  rw [setIntegral_prod _ hint]
  congr 1
  ext v
  exact integral_div ((v:ℂ)^3) (fun z => g (cuspCoordinateLift (v,z)))

lemma spatialComplexSplit_symm_eq (q : ℝ × ℂ) :
    spatialComplexSplit.symm q=WithLp.toLp 2 ![q.2.re,q.2.im,q.1] := by
  apply spatialComplexSplit.injective
  rw [spatialComplexSplit.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (Complex.re_add_im q.2).symm

lemma spatialComplexSplit_symm_continuous : Continuous spatialComplexSplit.symm := by
  change Continuous (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  fun_prop

lemma cuspCoordinateLift_continuousAt (q : ℝ × ℂ) (hq : 0<q.1) :
    ContinuousAt cuspCoordinateLift q := by
  have hp : 0<(spatialComplexSplit.symm q) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hq
  exact (euclideanToHyperbolic_contMDiffAt _ hp).continuousAt.comp
    spatialComplexSplit_symm_continuous.continuousAt

lemma cuspCoordinateLift_weighted_integrable (g : HyperbolicSpace→ℂ) (hg : Continuous g) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume := by
  let radiusBound : ℝ := ∑i,‖periodBasis i‖
  have hc : ContinuousOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ Metric.closedBall (0:ℂ) radiusBound) := by
    intro q hq
    have hpos : 0<q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
    exact ((hg.continuousAt.comp (cuspCoordinateLift_continuousAt q hpos)).div
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.pow 3)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousWithinAt
  apply (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
  intro q hq
  refine ⟨hq.1,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain q.2 hq.2


#print axioms cuspPeriodStrip_integral_coordinates
#print axioms cuspCoordinateLift_weighted_integrable
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
