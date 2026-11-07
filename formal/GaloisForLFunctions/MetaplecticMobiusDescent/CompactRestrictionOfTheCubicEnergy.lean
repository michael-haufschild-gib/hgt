/-
Compact restriction on the quotient is adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicGradientIsClosable
import GaloisForLFunctions.MetaplecticMobiusDescent.CompactCubicEnergyLocalizations
import GaloisForLFunctions.MetaplecticMobiusDescent.CompactCutoffCharts
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.AUnitaryWithCompactDefectHasCompleteEigenvectors

/-!
# Compact mass restriction on the cubic quotient

Every compact quotient set is covered by finitely many regions where a
smooth cutoff exceeds one half. Bounded hyperbolic density on each chart
controls its mass by the corresponding Euclidean localization. Those
localizations are compact, so their finite product is compact. Norm
domination then makes restriction of the completed energy space compact.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma compact_finite_pi {E G ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T : ι→E→L[ℂ]G) (hT : ∀i,IsCompactOperator (T i)) :
    IsCompactOperator (ContinuousLinearMap.pi T) := by
  let K : ι→Set G := fun i => closure ((T i) '' Metric.ball (0 : E) 1)
  have hK : ∀i,IsCompact (K i) := fun i => (hT i).isCompact_closure_image_ball 1
  refine ⟨Set.pi Set.univ K,isCompact_univ_pi hK,?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ)<1))
  intro x hx
  exact fun i hi => subset_closure ⟨x,hx,rfl⟩
lemma kernelChartCore_mass_estimate (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (H : ℝ) (hH : 0≤H) (hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H)
    (f : kernelSmoothTests) :
    (∫q in kernelChartCoreImage χ,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
      4*H*‖kernelL2Localize χ (kernelSmoothTestsToL2 f)‖^2 := by
  let S := kernelChartCore χ
  have hS : MeasurableSet S := (kernelChartCore_open χ).measurableSet
  have hpos : S⊆euclideanUpperHalf := (kernelChartCore_subset χ).trans χ.positive
  have hi : Set.InjOn kernelEuclideanProjection S := hinj.mono (kernelChartCore_subset χ)
  have hm := hyperbolicVolume_le_densityBound S hS hpos H
    (fun p hp => hdensity p (kernelChartCore_subset χ hp))
  have hloc : Integrable (fun p => ‖kernelLocalizedField χ f p‖^2) volume := by
    exact ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq
  have hlocHyp : IntegrableOn (fun p => ‖kernelLocalizedField χ f p‖^2) S hyperbolicEuclideanVolume :=
    (hloc.integrableOn.smul_measure (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top).mono_measure hm
  have hmass : IntegrableOn (fun p => ‖kernelTestField f p‖^2) S hyperbolicEuclideanVolume :=
    (kernelEuclideanProjection_measurePreserving_on S hS hpos hi).integrable_comp_of_integrable
      (kernelSmoothTests_memLp f).norm.integrable_sq.integrableOn
  rw [kernelL2Localize_core χ hinj,schwartz_toL2_norm_sq]
  have hEq := kernelEuclideanProjection_integral S hS hpos hi
    (fun q => ‖f.1 q‖^2) (kernelSmoothTests_memLp f).norm.integrable_sq.aestronglyMeasurable
  change (∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)=_ at hEq
  change (∫q in kernelEuclideanProjection '' S,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
    4*H*(∫p,‖kernelLocalizedField χ f p‖^2)
  rw [←hEq]
  calc
    _ ≤ ∫p in S,4*‖kernelLocalizedField χ f p‖^2∂hyperbolicEuclideanVolume := by
      apply setIntegral_mono_on hmass (hlocHyp.const_mul 4) hS
      intro p hp
      have hc : (1/2 : ℝ)<χ.func p := hp
      rw [kernelLocalizedField,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      have hn := sq_nonneg ‖kernelTestField f p‖
      have hx : 1≤4*(χ.func p)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hx hn]
    _ = 4*(∫p in S,‖kernelLocalizedField χ f p‖^2∂hyperbolicEuclideanVolume) := integral_const_mul _ _
    _ ≤ 4*(H*(∫p in S,‖kernelLocalizedField χ f p‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hh := integral_mono_measure hm
        (Eventually.of_forall (fun p => sq_nonneg ‖kernelLocalizedField χ f p‖))
        (hloc.integrableOn.smul_measure (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top)
      simpa only [integral_smul_measure,ENNReal.toReal_ofReal hH,smul_eq_mul] using hh
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_le_integral hloc (Eventually.of_forall (fun p => sq_nonneg ‖kernelLocalizedField χ f p‖))

lemma kernelChartCore_mass_bound (χ : KernelGoodCutoff) : ∃C : ℝ,0≤C ∧
    ∀f : kernelSmoothTests,
      (∫q in kernelChartCoreImage χ.1,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        C*‖kernelL2Localize χ.1 (kernelSmoothTestsToL2 f)‖^2 := by
  have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) (tsupport χ.1.func) :=
    (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.1.positive hp)))
  obtain ⟨r,hr⟩ := χ.1.compact.bddAbove_image hrho
  refine ⟨4*max 0 r,by positivity,fun f => ?_⟩
  exact kernelChartCore_mass_estimate χ.1 χ.2 (max 0 r) (le_max_left _ _)
    (fun p hp => (hr ⟨p,hp,rfl⟩).trans (le_max_right _ _)) f
/-- Restriction to a measurable quotient set, extended by zero. -/
def kernelMassRestrictionCLM (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  _root_.RHTower.lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ)
    (integralQuotientVolume globalKubotaKernel) 2 K hK

lemma kernelMassRestriction_coe (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) :
    (kernelMassRestrictionCLM K hK f : KernelQuotient → ℂ)
      =ᵐ[integralQuotientVolume globalKubotaKernel] K.indicator f :=
  _root_.RHTower.lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ)
    (integralQuotientVolume globalKubotaKernel) 2 K hK f

lemma kernelMassRestriction_norm_le (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) : ‖kernelMassRestrictionCLM K hK f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [kernelMassRestriction_coe K hK f] with q hq
  rw [hq]
  by_cases hm : q ∈ K
  · simp only [Set.indicator_of_mem hm, le_refl]
  · simp only [Set.indicator_of_notMem hm, norm_zero, norm_nonneg]

lemma kernelMassRestriction_norm_sq (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) :
    ‖kernelMassRestrictionCLM K hK f‖^2=
      ∫q in K,‖f q‖^2∂integralQuotientVolume globalKubotaKernel := by
  rw [←integral_indicator hK]
  calc
    _ = inner ℝ (kernelMassRestrictionCLM K hK f) (kernelMassRestrictionCLM K hK f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫q,inner ℝ (kernelMassRestrictionCLM K hK f q) (kernelMassRestrictionCLM K hK f q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [kernelMassRestriction_coe K hK f] with q hq
      rw [hq,real_inner_self_eq_norm_sq]
      by_cases hqK : q∈K
      · simp only [Set.indicator_of_mem hqK]
      · simp only [Set.indicator_of_notMem hqK,norm_zero,zero_pow (by decide : 2≠0)]

lemma kernelMassRestriction_smooth_norm_sq (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : kernelSmoothTests) :
    ‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2=
      ∫q in K,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel := by
  rw [kernelMassRestriction_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (kernelSmoothTests_memLp f).coeFn_toLp] with q hq
  change ‖((kernelSmoothTests_memLp f).toLp f.1) q‖^2=‖f.1 q‖^2
  rw [hq]

def kernelEnergyMassRestriction (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelEnergyGraph→L[ℂ]KernelQuotientL2 :=
  (kernelMassRestrictionCLM K hK).comp kernelEnergyMass

lemma integral_le_finite_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) (K : Set X) (hK : MeasurableSet K) (U : ι→Set X)
    (hU : ∀i,MeasurableSet (U i)) (hcover : K⊆⋃i,U i)
    (g : X→ℝ) (hg : Integrable g ν) (hn : ∀x,0≤g x) :
    (∫x in K,g x∂ν)≤∑i,∫x in U i,g x∂ν := by
  have hi : ∀i,Integrable ((U i).indicator g) ν := fun i => hg.indicator (hU i)
  calc
    _ = ∫x,K.indicator g x∂ν := (integral_indicator hK).symm
    _ ≤ ∫x,∑i,(U i).indicator g x∂ν := by
      apply integral_mono (hg.indicator hK) (integrable_finsetSum _ (fun i himem => hi i))
      intro x
      have hnon : ∀i,0≤(U i).indicator g x := fun i => Set.indicator_nonneg (fun y hy => hn y) x
      by_cases hx : x∈K
      · rw [Set.indicator_of_mem hx]
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover hx)
        calc
          g x=(U i).indicator g x := (Set.indicator_of_mem hi g).symm
          _ ≤ ∑j,(U j).indicator g x := Finset.single_le_sum (fun j hj => hnon j) (Finset.mem_univ i)
      · rw [Set.indicator_of_notMem hx]
        exact Finset.sum_nonneg (fun i hi => hnon i)
    _ = _ := by
      rw [integral_finsetSum _ (fun i himem => hi i)]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_indicator (hU i)

def kernelEnergyChartFamily (t : Finset KernelGoodCutoff) :
    KernelEnergyGraph→L[ℂ](t→EuclideanL2) :=
  ContinuousLinearMap.pi (fun χ : t => kernelEnergyLocalizeL2 χ.1.1)

lemma kernelEnergyChartFamily_isCompact (t : Finset KernelGoodCutoff) :
    IsCompactOperator (kernelEnergyChartFamily t) :=
  compact_finite_pi _ (fun χ => kernelEnergyLocalizeL2_isCompact χ.1.1 χ.1.2)

lemma finite_sum_weighted_norm_sq_le {G ι : Type*} [Fintype ι]
    [NormedAddCommGroup G] (C : ι→ℝ) (hC : ∀i,0≤C i) (x : ι→G) :
    (∑i,C i*‖x i‖^2)≤(∑i,C i)*‖x‖^2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2) (hC i)

lemma kernelEnergyChartFamily_core_apply (t : Finset KernelGoodCutoff)
    (f : kernelSmoothTests) (χ : t) :
    kernelEnergyChartFamily t (kernelEnergyGraphCore f) χ=
      kernelL2Localize χ.1.1 (kernelSmoothTestsToL2 f) := by
  change kernelL2Localize χ.1.1 (kernelEnergyMass (kernelEnergyGraphCore f))=_
  rw [kernelEnergyMass_core]

lemma kernelCompact_mass_bound (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      (∫q in K,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        C*‖kernelEnergyChartFamily t (kernelEnergyGraphCore f)‖^2 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover K hK
  have hcov : K⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  choose C hC hbound using fun χ : t => kernelChartCore_mass_bound χ.1
  refine ⟨t,∑χ,C χ,Finset.sum_nonneg (fun χ hχ => hC χ),fun f => ?_⟩
  calc
    _ ≤ ∑χ : t,∫q in kernelChartCoreImage χ.1.1,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel :=
      integral_le_finite_cover _ K hK.measurableSet _
        (fun χ : t => (kernelChartCoreImage_open χ.1.1).measurableSet) hcov _
        (kernelSmoothTests_memLp f).norm.integrable_sq (fun _ => sq_nonneg _)
    _ ≤ ∑χ : t,C χ*‖kernelL2Localize χ.1.1 (kernelSmoothTestsToL2 f)‖^2 :=
      Finset.sum_le_sum (fun χ hχ => hbound χ f)
    _ = ∑χ : t,C χ*‖kernelEnergyChartFamily t (kernelEnergyGraphCore f) χ‖^2 := by
      simp only [kernelEnergyChartFamily_core_apply]
    _ ≤ _ := finite_sum_weighted_norm_sq_le C hC _

theorem kernelEnergyMassRestriction_isCompact (K : Set KernelQuotient) (hK : IsCompact K) :
    IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) := by
  obtain ⟨t,C,hC,hbound⟩ := kernelCompact_mass_bound K hK
  have hsq : ∀u : KernelEnergyGraph,
      ‖kernelEnergyMassRestriction K hK.measurableSet u‖^2≤
        C*‖kernelEnergyChartFamily t u‖^2 := by
    intro u
    exact kernelEnergyGraphCore_dense.induction_on u
      (isClosed_le (by fun_prop : Continuous (fun v => ‖kernelEnergyMassRestriction K hK.measurableSet v‖^2))
        (by fun_prop : Continuous (fun v => C*‖kernelEnergyChartFamily t v‖^2)))
      (fun f => by
        change ‖kernelMassRestrictionCLM K hK.measurableSet
          (kernelEnergyMass (kernelEnergyGraphCore f))‖^2≤_
        rw [kernelEnergyMass_core,kernelMassRestriction_smooth_norm_sq]
        exact hbound f)
  apply GaloisForLFunctions.CanonicalSystemOfTheWindowTower.isCompactOperator_of_norm_le
    (kernelEnergyChartFamily_isCompact t) (C := Real.sqrt C)
  intro u
  have hs := hsq u
  have hc := Real.sq_sqrt hC
  have hn := mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (kernelEnergyChartFamily t u))
  have he : (Real.sqrt C*‖kernelEnergyChartFamily t u‖)^2=C*‖kernelEnergyChartFamily t u‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  nlinarith [norm_nonneg (kernelEnergyMassRestriction K hK.measurableSet u)]

#print axioms kernelChartCore_mass_bound
#print axioms kernelCompact_mass_bound
#print axioms kernelEnergyMassRestriction_isCompact
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
