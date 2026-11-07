/-
Cubic cusp averages adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicCuspPeriodLattice
import GaloisForLFunctions.MetaplecticMobiusDescent.SmoothCubicExhaustion
import GaloisForLFunctions.MetaplecticMobiusDescent.LocalCubicCorrectedSeeds

/-!
# Bounded cusp averages detect the incoming residue

The high-cusp height-product obstruction makes a period strip injective
on the cubic kernel quotient. Exact volume transport turns its integral
into a bounded quotient L² functional. Applying it to the locally corrected
family preserves meromorphy and the explicit residue limit.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma levelThree_integral_eq_translation (M : CubicKubota.levelThree)
    (hc : (M : SL(2,O)) 1 0=0) :
    integralComplexMatrix M.1=complexTranslation (ringComplex ((M : SL(2,O)) 0 1)) := by
  have hr := row_eq_one_of_lower_left_zero M hc
  have hd : (M : SL(2,O)) 1 1=1 := by
    simpa [row,Matrix.one_apply] using congrFun hr 1
  have ha : (M : SL(2,O)) 0 0=1 := by
    have hh : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1-
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0=1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
    simpa only [hc,hd,mul_zero,mul_one,sub_zero] using hh
  have hentry (i j : Fin 2) :
      integralComplexMatrix (M : SL(2,O)) i j=ringComplex ((M : SL(2,O)) i j) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hentry,complexTranslation,ha,hc,hd]

lemma periodDomain_unique_translate (z w t : ℂ) (hz : z∈periodDomain) (hw : w∈periodDomain)
    (ht : t∈periodLattice) (he : z=w+t) : z=w := by
  have hf := ZSpan.fract_add_ZSpan periodBasis w ht
  rw [←he,(ZSpan.fract_eq_self (b := periodBasis)).mpr hz,
    (ZSpan.fract_eq_self (b := periodBasis)).mpr hw] at hf
  exact hf

def cuspPeriodRegion : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ 1<hyperbolicHeight w}

lemma cuspPeriodRegion_measurable : MeasurableSet cuspPeriodRegion :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Ioi.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodRegion_injective :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) cuspPeriodRegion := by
  intro u hu v hv he
  obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff globalKubotaKernel u v).mp he
  have hMu : integralComplexMatrix (M:SL(2,O)) • v=u := hM
  have hc : (M:SL(2,O)) 1 0=0 := by
    by_contra hn
    have hb := integral_hyperbolicHeight_mul_le_one (M:SL(2,O)) hn v
    rw [hMu] at hb
    have huh : 1<hyperbolicHeight u := hu.2
    have hvh : 1<hyperbolicHeight v := hv.2
    nlinarith only [hb,huh,hvh,mul_pos (sub_pos.mpr huh) (sub_pos.mpr hvh)]
  let N : CubicKubota.levelThree := ⟨M,globalKubotaKernel_le_levelThree M.2⟩
  have ht := levelThree_integral_eq_translation N hc
  obtain ⟨z,t,htpos,hvrep⟩ := upperPoint_surjective v
  have hua : u=upperPoint (z+ringComplex ((M:SL(2,O)) 0 1)) t htpos := by
    rw [←hMu,←hvrep,ht,complexTranslation_action]
  have hvl : hyperbolicHorizontal v=z := by rw [←hvrep,hyperbolicHorizontal_upperPoint]
  have hul : hyperbolicHorizontal u=z+ringComplex ((M:SL(2,O)) 0 1) := by
    rw [hua,hyperbolicHorizontal_upperPoint]
  obtain ⟨k,hk⟩ := CubicKubota.levelThree_upper N
  have hper : ringComplex ((M:SL(2,O)) 0 1)∈periodLattice := by
    change ringComplex ((N:CubicKubota.levelThree).1 0 1)∈periodLattice
    rw [hk,map_mul,map_ofNat]
    exact three_embedding_mem k
  have hehor : hyperbolicHorizontal u=hyperbolicHorizontal v :=
    periodDomain_unique_translate _ _ _ hu.1 hv.1 hper (by rw [hul,hvl])
  have hez : z+ringComplex ((M:SL(2,O)) 0 1)=z := by
    simpa only [hul,hvl] using hehor
  rw [hua,hez,←hvrep]

def cuspPeriodStrip (a b : ℝ) : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ hyperbolicHeight w∈Set.Icc a b}

lemma cuspPeriodStrip_measurable (a b : ℝ) : MeasurableSet (cuspPeriodStrip a b) :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Icc.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodStrip_injective (a b : ℝ) (ha : 1<a) :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) (cuspPeriodStrip a b) := by
  apply kernelProjection_cuspPeriodRegion_injective.mono
  intro w hw
  exact ⟨hw.1,ha.trans_le hw.2.1⟩

lemma kernelProjection_cuspPeriodStrip_measurePreserving (a b : ℝ) (ha : 1<a) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      ((integralQuotientVolume globalKubotaKernel).restrict
        (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip a b)) :=
  kernelProjection_measurePreserving_on _ (cuspPeriodStrip_measurable a b)
    (kernelProjection_cuspPeriodStrip_injective a b ha)


open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

def kernelCuspStripSet : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6

lemma kernelCuspStripSet_measurable : MeasurableSet kernelCuspStripSet :=
  (cuspPeriodStrip_measurable 5 6).image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn
    (kernelProjection_cuspPeriodStrip_injective 5 6 (by norm_num))

def kernelCuspStripAverage : KernelQuotientL2→L[ℂ]ℂ :=
  innerSL ℂ (indicatorConstLp 2 kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) (1:ℂ))

lemma kernelCuspStripAverage_apply (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫q in kernelCuspStripSet,F q∂integralQuotientVolume globalKubotaKernel :=
  L2.inner_indicatorConstLp_one kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) F

lemma kernelCuspStripAverage_hyperbolic (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspStripAverage_apply]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := (Lp.aestronglyMeasurable F).mono_measure (Measure.restrict_le_self (s := kernelCuspStripSet))
  change AEStronglyMeasurable F ((integralQuotientVolume globalKubotaKernel).restrict
    (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6)) at hh
  change (∫q in integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6,
    F q∂integralQuotientVolume globalKubotaKernel)=_
  rw [←hm.map_eq] at hh ⊢
  exact integral_map hm.measurable.aemeasurable hh

def kernelCuspAverageCompact : Set KernelQuotient :=
  {q | kernelQuotientBarrier 2 3 q≤6}

lemma kernelCuspAverageCompact_isCompact : IsCompact kernelCuspAverageCompact :=
  kernelBarrier_sublevel_isCompact 6

lemma kernelCuspStripSet_subset_compact : kernelCuspStripSet⊆kernelCuspAverageCompact := by
  rintro q ⟨w,hw,rfl⟩
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  have hfive : 5≤v := by simpa only [hyperbolicHeight_upperPoint] using hw.2.1
  have hsix : v≤6 := by simpa only [hyperbolicHeight_upperPoint] using hw.2.2
  change cuspBarrier 2 3 (upperPoint z v hv)≤6
  have hh := cuspBarrier_high 2 3 (by norm_num) (by norm_num) 1 z v hv (by linarith)
  simpa only [map_one,one_smul] using hh.le.trans hsix

lemma kernelCuspStripAverage_restrict (F : KernelQuotientL2) :
    kernelCuspStripAverage (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspStripAverage F := by
  rw [kernelCuspStripAverage_apply,kernelCuspStripAverage_apply]
  apply setIntegral_congr_ae kernelCuspStripSet_measurable
  filter_upwards [kernelMassRestriction_coe kernelCuspAverageCompact
    kernelCuspAverageCompact_isCompact.measurableSet F] with q hq
  intro hmem
  exact hq.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact hmem) F)

def kernelCuspAverageFamily (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspStripAverage
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspAverageFamily_meromorphicAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelCuspAverageFamily a b ha hab) (4/3:ℂ) :=
  meromorphicAt_clm kernelCuspStripAverage
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)

lemma kernelCuspAverageFamily_residue_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspAverageFamily a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := kernelCuspStripAverage.continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspStripAverage_restrict,kernelCuspAverageFamily] using hh

lemma kernelCuspAverageFamily_actual_integral (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspAverageFamily a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspAverageFamily,kernelCuspStripAverage_hyperbolic]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hlocal := kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s
  have hrestr := ae_restrict_of_ae hlocal (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  apply integral_congr_ae
  filter_upwards [hp,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _)

#print axioms kernelProjection_cuspPeriodStrip_measurePreserving
#print axioms kernelCuspAverageFamily_meromorphicAt
#print axioms kernelCuspAverageFamily_residue_limit
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
