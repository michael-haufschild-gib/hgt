/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license; see LICENSE and NOTICE in the parent directory.
Adapted from rellich-kondrachov, Euclidean/Rellich.lean.
The compact C¹ family reduction also follows OpenAI, CubicSieve/RadialWindows.lean.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.TranslationEnergyBound
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.SmoothingCompactnessCriterion
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.SmallProbabilityKernels
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.SmoothedTranslationBound

/-!
# Rellich compactness on a fixed Euclidean support

The energy unit ball has a uniform translation modulus. Small probability
kernels approximate it uniformly in `L²`; each smoothing operator is compact.
Thus the mass projection of the supported energy graph is compact.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance rellichMeasurableSpace : MeasurableSpace E := borel E
local instance rellichBorelSpace : BorelSpace E := ⟨rfl⟩

/-- Energy vectors whose mass component is supported in `K` almost everywhere. -/
def h1On (K : Set E) (hKm : MeasurableSet K) : Submodule ℝ (h1 (volume : Measure E)) :=
  Submodule.comap (h1ToL2 (volume : Measure E)).toLinearMap
    (LinearMap.range (LpExtension.extendIsometry (μ := (volume : Measure E))
      (E := ℝ) (p := (2:ℝ≥0∞)) hKm).toLinearMap)

/-- Mass projection restricted to the supported energy graph. -/
def h1OnToL2 (K : Set E) (hKm : MeasurableSet K) :
    h1On K hKm →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  (h1ToL2 (volume : Measure E)).comp (h1On K hKm).subtypeL

lemma h1OnToL2_norm_le (K : Set E) (hKm : MeasurableSet K) (u : h1On K hKm) :
    ‖h1OnToL2 K hKm u‖≤‖u‖ := norm_fst_le (x := u.val.val)

lemma h1ToL2Grad_norm_le (u : h1 (volume : Measure E)) :
    ‖h1ToL2Grad (volume : Measure E) u‖≤‖u‖ := norm_snd_le (x := u.val)

lemma h1On_translation_modulus (K : Set E) (hKm : MeasurableSet K)
    (u : h1On K hKm) (hu : ‖u‖≤1) {δ : ℝ} (hδ : 0≤δ)
    (t : E) (ht : t∈Metric.ball 0 δ) :
    ‖translateL2 (volume : Measure E) (-t) (h1OnToL2 K hKm u)-h1OnToL2 K hKm u‖≤δ := by
  have hg : ‖h1ToL2Grad (volume : Measure E) u.1‖≤1 :=
    (h1ToL2Grad_norm_le u.1).trans hu
  have ht' : ‖t‖≤δ := (mem_ball_zero_iff.mp ht).le
  have hb := norm_translateL2_sub_h1ToL2_le (volume : Measure E) (-t) u.1
  change ‖translateL2 (volume : Measure E) (-t) (h1OnToL2 K hKm u)-h1OnToL2 K hKm u‖≤
    ‖-t‖*‖h1ToL2Grad (volume : Measure E) u.1‖ at hb
  rw [norm_neg] at hb
  exact hb.trans ((mul_le_mul ht' hg (norm_nonneg _) hδ).trans_eq (mul_one δ))

/-- The mass image of the supported energy unit ball has compact closure. -/
lemma h1OnToL2_unitBall_compact (K : Set E) (hK : IsCompact K) (hKm : MeasurableSet K) :
    IsCompact (closure (h1OnToL2 K hKm '' Metric.closedBall (0 : h1On K hKm) 1)) := by
  let T := h1OnToL2 K hKm
  let A : Set (Lp ℝ 2 (volume.restrict K)) :=
    {u | L2Compactness.extendByZeroL2 hKm u∈T '' Metric.closedBall 0 1}
  have hA : A⊆Metric.closedBall (0 : Lp ℝ 2 (volume.restrict K)) 1 := by
    rintro u ⟨x,hx,he⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    rw [←L2Compactness.norm_extendByZeroL2 hKm u,←he]
    have hx' : ‖x‖≤(1:ℝ) := by
      simpa only [Metric.mem_closedBall,dist_zero_right x] using hx
    exact (h1OnToL2_norm_le K hKm x).trans hx'
  have hApprox : ∀ε : ℝ,0<ε → ∃ψ : E→ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧
      (∀x,0≤ψ x) ∧ (∫x,ψ x ∂(volume : Measure E))=1 ∧ ∀u∈A,
      (∫t,‖translateL2 (volume : Measure E) (-t) (L2Compactness.extendByZeroL2 hKm u)-
        L2Compactness.extendByZeroL2 hKm u‖^2∂L2Compactness.kernelMeasure ψ)≤(ε/2)^2 := by
    intro ε hε
    obtain ⟨ψ,hc,hs,hpos,hint,hsupp⟩ :=
      L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one (E := E) (half_pos hε)
    refine ⟨ψ,hc,hs,hpos,hint,?_⟩
    rintro u ⟨x,hx,he⟩
    rw [←he]
    apply L2Compactness.translation_average_le_of_local_bound
      hc hs hpos hint (half_pos hε).le hsupp
    have hx' : ‖x‖≤(1:ℝ) := by
      simpa only [Metric.mem_closedBall,dist_zero_right x] using hx
    exact h1On_translation_modulus K hKm x hx' (half_pos hε).le
  have himage : T '' Metric.closedBall 0 1=L2Compactness.extendByZeroL2 hKm '' A := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨u,hu⟩ := x.property
      refine ⟨u,?_,hu⟩
      exact ⟨x,hx,hu.symm⟩
    · rintro ⟨u,hu,rfl⟩
      exact hu
  rw [show h1OnToL2 K hKm=T from rfl,himage]
  exact L2Compactness.compact_closure_of_small_translation_average
    hK hKm hA hApprox

/-- Compact restriction of the complete Euclidean energy graph to a fixed support. -/
theorem isCompactOperator_h1OnToL2 (K : Set E) (hK : IsCompact K) (hKm : MeasurableSet K) :
    IsCompactOperator (h1OnToL2 K hKm) := by
  refine ⟨closure (h1OnToL2 K hKm '' Metric.closedBall (0 : h1On K hKm) 1),
    h1OnToL2_unitBall_compact K hK hKm,?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : h1On K hKm) zero_lt_one)
  intro x hx
  exact subset_closure ⟨x,Metric.ball_subset_closedBall hx,rfl⟩

/-- A compactly supported `C¹` function determines a vector in the complete energy graph. -/
def c1cToH1 (f : C1c (E := E)) : h1 (volume : Measure E) :=
  ⟨graph (volume : Measure E) f,
    (LinearMap.range (graph (volume : Measure E))).le_topologicalClosure ⟨f,rfl⟩⟩

lemma c1c_supported_range (K : Set E) (hK : MeasurableSet K)
    (f : C1c (E := E)) (hf : Function.support f.1⊆K) :
    toL2 (volume : Measure E) f∈LinearMap.range
      (LpExtension.extendIsometry (μ := (volume : Measure E)) (p := (2:ℝ≥0∞)) hK).toLinearMap := by
  have hmem := memLp_of_mem_C1c (volume : Measure E) f.2
  have hres : MemLp f.1 2 (volume.restrict K) := hmem.mono_measure Measure.restrict_le_self
  refine ⟨hres.toLp f.1,?_⟩
  apply Lp.ext
  have hr : ∀ᵐx ∂(volume : Measure E),x∈K→hres.toLp f.1 x=f.1 x :=
    (ae_restrict_iff' hK).mp hres.coeFn_toLp
  have hg : (toL2 (volume : Measure E) f : E→ℝ)=ᵐ[volume]f.1 := hmem.coeFn_toLp
  filter_upwards [LpExtension.extendIsometry_coe hK (hres.toLp f.1),hr,hg]
    with x hx hrx hgx
  change LpExtension.extendIsometry hK (hres.toLp f.1) x=toL2 (volume : Measure E) f x
  rw [hx,hgx]
  by_cases hxm : x∈K
  · simpa only [Set.indicator_of_mem hxm] using hrx hxm
  · rw [Set.indicator_of_notMem hxm]
    symm
    by_contra hne
    exact hxm (hf hne)

def c1cToSupportedH1 (K : Set E) (hK : MeasurableSet K)
    (f : C1c (E := E)) (hf : Function.support f.1⊆K) : h1On K hK :=
  ⟨c1cToH1 f,c1c_supported_range K hK f hf⟩

private lemma compact_clm_closedBall {V W : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (hT : IsCompactOperator T) (R : ℝ) :
    IsCompact (closure (T '' Metric.closedBall 0 R)) :=
  IsCompactOperator.isCompact_closure_image_closedBall (f := T.toLinearMap) hT R

/-- Common compact support and bounded mass and gradient give `L²` precompactness. -/
theorem c1c_family_precompact (K : Set E) (hK : IsCompact K)
    (family : Set (C1c (E := E))) (R : ℝ)
    (hsupp : ∀f∈family,Function.support f.1⊆K)
    (hmass : ∀f∈family,‖toL2 (volume : Measure E) f‖≤R)
    (hgrad : ∀f∈family,‖toL2Grad (volume : Measure E) f‖≤R) :
    IsCompact (closure (toL2 (volume : Measure E) '' family)) := by
  have hc := compact_clm_closedBall
    (V := h1On K hK.measurableSet) (W := Lp ℝ 2 (volume : Measure E))
    (h1OnToL2 K hK.measurableSet)
    (isCompactOperator_h1OnToL2 K hK hK.measurableSet) R
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨c1cToSupportedH1 K hK.measurableSet f (hsupp f hf),?_,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right (c1cToSupportedH1 K hK.measurableSet f (hsupp f hf))]
  change max ‖toL2 (volume : Measure E) f‖ ‖toL2Grad (volume : Measure E) f‖≤R
  exact max_le (hmass f hf) (hgrad f hf)

#print axioms c1c_family_precompact

#print axioms isCompactOperator_h1OnToL2
end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev
