import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerExponentialSolvability
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogOperatorContinuity

/-! # Convolution automorphisms in the original Frechet topology

Admission plus faithful continuous Mellin observations closes each multiplier
graph. The already-proved Frechet open mapping theorem then supplies
continuity, without changing the source topology or imposing a norm bound.
-/

open Set Topology Uniformity MeasureTheory
namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

local notation "V" => DeningerMeyerStrongLogTarget

/-- Every displayed convolution integral is absolutely admitted at every source point. -/
theorem deningerMeyerSourceConvolution_integrable (g h : V) (x : ℝ) :
    Integrable (fun t : ℝ => g.val t * h.val (x-t)) := by
  let G := (DeningerMeyerSource.toSource (deningerMeyerStrongLogSourceEquiv g)).val
  let H := (DeningerMeyerSource.toSource (deningerMeyerStrongLogSourceEquiv h)).val
  change Integrable (fun t : ℝ => G t * H (x-t))
  exact G.integrable.mul_bdd
    (H.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => H.norm_le_seminorm ℂ (x-t))

theorem deningerMeyerExponentialEquation_existsUnique_integrable (g f : V) :
    ∃! h : V,
      (∀ x : ℝ, h.val x +
        (∫ t : ℝ, (deningerMeyerSourceExp g).val t * h.val (x-t)) = f.val x) ∧
      ∀ x : ℝ, Integrable (fun t : ℝ => (deningerMeyerSourceExp g).val t * h.val (x-t)) := by
  obtain ⟨h, hh, huniq⟩ := deningerMeyerExponentialEquation_existsUnique g f
  exact ⟨h, ⟨hh, fun x => deningerMeyerSourceConvolution_integrable _ _ x⟩,
    fun k hk => huniq k hk.1⟩

private theorem source_closed_graph (T : V →ₗ[ℂ] V)
    (hT : IsClosed (T.graph : Set (V × V))) : Continuous T := by
  letI : UniformSpace V := DeningerMeyerNaturalTopology.strongLogUniformSpace
  letI : (𝓤 V).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace V := by infer_instance
  letI : CompleteSpace T.graph := completeSpace_coe_iff_isComplete.mpr hT.isComplete
  letI : IsUniformAddGroup T.graph :=
    inferInstanceAs (IsUniformAddGroup T.graph.toAddSubgroup)
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace T.graph :=
    hT.isCompletelyPseudoMetrizableSpace
  let φ₀ : V →ₗ[ℂ] V × V := LinearMap.id.prod T
  have hleft : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : V ≃ₗ[ℂ] T.graph :=
    (LinearEquiv.ofLeftInverse hleft).trans
      (LinearEquiv.ofEq _ _ T.graph_eq_range_prod.symm)
  have hc : Continuous φ.symm := continuous_subtype_val.fst
  have hi : Continuous φ := by
    simpa only [LinearEquiv.symm_symm] using
      (GaloisForLFunctions.continuous_symm_of_continuous
        (𝕜 := ℂ) (E := T.graph) (F := V) φ.symm hc)
  exact (continuous_subtype_val.comp hi).snd

private theorem sourceMellin_continuous (s : ℂ) :
    Continuous (fun g : V => deningerMeyerStrongLogMellin g s) :=
  deningerMeyerStrongLogMellinJetLM_continuous 0 s

/-- Actual convolution acts continuously in the unchanged all-weight source topology. -/
theorem deningerMeyerSourceConvolution_continuous (g : V) :
    Continuous (deningerMeyerSourceConvolution g) := by
  apply source_closed_graph (deningerMeyerSourceConvolutionLM g)
  have he : ((deningerMeyerSourceConvolutionLM g).graph : Set (V × V)) =
      ⋂ s : ℂ, {p | deningerMeyerStrongLogMellin p.2 s =
        deningerMeyerStrongLogMellin g s * deningerMeyerStrongLogMellin p.1 s} := by
    ext p
    change p.2 = deningerMeyerSourceConvolution g p.1 ↔ _
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun hp s => ?_, fun hp => ?_⟩
    · rw [hp, deningerMeyerSourceConvolution_mellin]
    · apply deningerMeyerStrongLogMellin_injective
      funext s
      exact (hp s).trans (deningerMeyerSourceConvolution_mellin g p.1 s).symm
  rw [he]
  exact isClosed_iInter fun s => isClosed_eq
    ((sourceMellin_continuous s).comp continuous_snd)
    (continuous_const.mul ((sourceMellin_continuous s).comp continuous_fst))

theorem deningerMeyerSourceGauge_continuous (g : V) :
    Continuous (deningerMeyerSourceGauge g) :=
  continuous_id.add (deningerMeyerSourceConvolution_continuous (deningerMeyerSourceExp g))

/-- Global exponential inversion is stable in every original Meyer source seminorm. -/
def deningerMeyerSourceGaugeContinuousEquiv (g : V) : V ≃L[ℂ] V where
  toLinearEquiv := deningerMeyerSourceGaugeEquiv g
  continuous_toFun := deningerMeyerSourceGauge_continuous g
  continuous_invFun := deningerMeyerSourceGauge_continuous (-g)

theorem deningerMeyerCohomologySourceGauge_continuous (g : V) :
    Continuous (deningerMeyerCohomologySourceGauge g) := by
  apply (LinearMap.range deningerMeyerStrongLogSumLM).isQuotientMap_mkQ.continuous_iff.mpr
  exact continuous_quot_mk.comp (deningerMeyerSourceGauge_continuous g)

/-- The descended automorphism and its inverse retain the original quotient topology. -/
def deningerMeyerCohomologySourceGaugeContinuousEquiv (g : V) :
    DeningerMeyerStrongLogCohomology ≃L[ℂ] DeningerMeyerStrongLogCohomology where
  toLinearEquiv := deningerMeyerCohomologySourceGaugeEquiv g
  continuous_toFun := deningerMeyerCohomologySourceGauge_continuous g
  continuous_invFun := deningerMeyerCohomologySourceGauge_continuous (-g)

end
end RHTower
