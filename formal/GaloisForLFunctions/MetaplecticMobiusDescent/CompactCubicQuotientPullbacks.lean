/-
Compact quotient pullbacks adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.LocalCubicCorrectedSeeds

/-!
# Bounded pullback over compact sets of hyperbolic space

A finite cover by injective quotient charts bounds the pushforward of
compactly restricted hyperbolic volume by a finite multiple of quotient
volume. The resulting dominated-measure map gives a bounded complex
linear pullback of the actual quotient `L²` functions.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

theorem kernelCompact_projection_measure_bound (K : Set HyperbolicSpace) (hK : IsCompact K) :
    ∃N : ℕ,Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (N:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel := by
  choose e he heq using kernelQuotient_localHomeomorph
  have hcover : K⊆⋃w : HyperbolicSpace,(e w).source := by
    intro w _
    exact Set.mem_iUnion.mpr ⟨w,he w⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun w => (e w).source) (fun w => (e w).open_source) hcover
  have hinj (w : HyperbolicSpace) :
      Set.InjOn (integralOrbitProjection globalKubotaKernel) (e w).source := by
    rw [heq w]
    exact (e w).injOn
  refine ⟨t.card,Measure.le_iff.mpr ?_⟩
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.smul_apply]
  change hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ K)≤
    (t.card:ℝ≥0∞)*integralQuotientVolume globalKubotaKernel B
  calc
    _ ≤ hyperbolicVolume (⋃w∈t,(integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) := by
      apply measure_mono
      rintro w ⟨hw,hK⟩
      obtain ⟨v,hv,hwv⟩ := Set.mem_iUnion₂.mp (ht hK)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,hw,hwv⟩
    _ ≤ ∑w∈t,hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑_w∈t,integralQuotientVolume globalKubotaKernel B := by
      apply Finset.sum_le_sum
      intro w hw
      have hm := kernelProjection_measurePreserving_on (e w).source (e w).open_source.measurableSet (hinj w)
      rw [←Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),
        ←Measure.map_apply (measurable_integralOrbitProjection _) hB,hm.map_eq]
      exact Measure.restrict_le_self B
    _ = _ := by simp [nsmul_eq_mul]

section DominatedComplexL2
variable {α : Type*} [MeasurableSpace α] {«μ» ν : Measure α} {c : ℝ≥0∞}

def dominatedComplexL2 (hc : c≠⊤) (h : ν≤c•«μ») : Lp ℂ 2 «μ»→L[ℂ]Lp ℂ 2 ν where
  toFun := Lp.LpToLpOfMeasureLeSMul hc h
  map_add' := map_add (Lp.LpToLpOfMeasureLeSMul hc h)
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hc h (z•f),
      Lp.coeFn_LpToLpOfMeasureLeSMul hc h f,
      Lp.coeFn_smul z (Lp.LpToLpOfMeasureLeSMul hc h f),
      (Measure.absolutelyContinuous_of_le_smul h).ae_eq (Lp.coeFn_smul z f)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,Pi.smul_apply] at *
    rw [h1,h3,h2,h4]
  cont := (Lp.LpToLpOfMeasureLeSMul hc h).continuous

lemma dominatedComplexL2_ae (hc : c≠⊤) (h : ν≤c•«μ») (f : Lp ℂ 2 «μ») :
    dominatedComplexL2 hc h f=ᵐ[ν]f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hc h f

lemma dominatedComplexL2_norm_le (hc : c≠⊤) (h : ν≤c•«μ») (f : Lp ℂ 2 «μ») :
    ‖dominatedComplexL2 hc h f‖≤c.toReal^((1:ℝ)/2)*‖f‖ := by
  have hb := (Lp.LpToLpOfMeasureLeSMul hc h : Lp ℂ 2 «μ»→L[ℝ]Lp ℂ 2 ν).le_opNorm f
  have hn := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) hc h
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using hn

end DominatedComplexL2

def kernelCompactMultiplicity (K : Set HyperbolicSpace) (hK : IsCompact K) : ℕ :=
  (kernelCompact_projection_measure_bound K hK).choose

lemma kernelCompactMultiplicity_spec (K : Set HyperbolicSpace) (hK : IsCompact K) :
    Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (kernelCompactMultiplicity K hK:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel :=
  (kernelCompact_projection_measure_bound K hK).choose_spec

def kernelCompactPullbackCLM (K : Set HyperbolicSpace) (hK : IsCompact K) :
    KernelQuotientL2→L[ℂ]Lp ℂ 2 (hyperbolicVolume.restrict K) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    ⟨measurable_integralOrbitProjection _,rfl⟩).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤)
        (kernelCompactMultiplicity_spec K hK))

theorem kernelCompactPullbackCLM_ae (K : Set HyperbolicSpace) (hK : IsCompact K)
    (F : KernelQuotientL2) :
    kernelCompactPullbackCLM K hK F=ᵐ[hyperbolicVolume.restrict K]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm : MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict K)
      (Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)) :=
    ⟨measurable_integralOrbitProjection _,rfl⟩
  have he := dominatedComplexL2_ae
    (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤) (kernelCompactMultiplicity_spec K hK) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans (hm.quasiMeasurePreserving.ae_eq_comp he)



#print axioms kernelCompact_projection_measure_bound
#print axioms kernelCompactPullbackCLM_ae
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
