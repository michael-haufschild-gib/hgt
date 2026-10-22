import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogSourceEquivalence
import GaloisForLFunctions.RHTower.Deninger.DeningerFrechetInstances
import GaloisForLFunctions.HTGeometry.FrechetOpenMapping
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# The literal all-weight Meyer cohomology is a separated complete source

The scoped instances use exactly the weighted-derivative source topology and
its actual quotient by Poisson boundaries. They do not replace that quotient
by its separation or a divisor model. Closedness and completeness now apply
to the same cohomology classes used by the causal constructions.
-/

open Filter Set Topology Uniformity TopologicalSpace

namespace RHTower
noncomputable section

namespace DeningerMeyerNaturalTopology

scoped instance strongLogTopology : TopologicalSpace DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogTopology

scoped instance strongLogTopologicalAddGroup : IsTopologicalAddGroup DeningerMeyerStrongLogTarget :=
  topologicalAddGroup_iInf
    (ts' := fun i : ℕ × ℤ => TopologicalSpace.induced
      (deningerMeyerStrongLogGaugeLinear i.1 i.2) inferInstance) fun i =>
    topologicalAddGroup_induced (deningerMeyerStrongLogGaugeLinear i.1 i.2)

scoped instance strongLogContinuousSMul : ContinuousSMul ℂ DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogTopology_continuousSMul

scoped instance strongLogUniformSpace : UniformSpace DeningerMeyerStrongLogTarget :=
  IsTopologicalAddGroup.rightUniformSpace DeningerMeyerStrongLogTarget

scoped instance strongLogUniformAddGroup : IsUniformAddGroup DeningerMeyerStrongLogTarget :=
  isUniformAddGroup_of_addCommGroup

scoped instance strongLogT2Space : T2Space DeningerMeyerStrongLogTarget :=
  T2Space.of_injective_continuous
    deningerMeyerStrongLogGaugeLinear_zero_zero_injective
    (continuous_deningerMeyerStrongLogGaugeLinear 0 0)

scoped instance strongLogFirstCountable : FirstCountableTopology DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogSourceContinuousEquiv.toHomeomorph.isInducing.firstCountableTopology

scoped instance strongLogComplete : CompleteSpace DeningerMeyerStrongLogTarget :=
  (completeSpace_congr (e := deningerMeyerStrongLogSourceContinuousEquiv.toEquiv)
    deningerMeyerStrongLogSourceContinuousEquiv.isUniformEmbedding).mpr
    inferInstance

scoped instance boundaryClosed :
    IsClosed (LinearMap.range deningerMeyerStrongLogSumLM : Set DeningerMeyerStrongLogTarget) :=
  deningerMeyerStrongLogSum_range_isClosed

scoped instance cohomologyT2Space : T2Space DeningerMeyerStrongLogCohomology :=
  inferInstanceAs (T2Space (DeningerMeyerStrongLogTarget ⧸
    LinearMap.range deningerMeyerStrongLogSumLM))

scoped instance cohomologyUniformSpace : UniformSpace DeningerMeyerStrongLogCohomology :=
  IsTopologicalAddGroup.rightUniformSpace DeningerMeyerStrongLogCohomology

scoped instance cohomologyUniformAddGroup : IsUniformAddGroup DeningerMeyerStrongLogCohomology :=
  isUniformAddGroup_of_addCommGroup

scoped instance cohomologyFirstCountable : FirstCountableTopology DeningerMeyerStrongLogCohomology := by
  let N := LinearMap.range deningerMeyerStrongLogSumLM
  refine ⟨fun q => ?_⟩
  obtain ⟨g, rfl⟩ := N.mkQ_surjective q
  rw [← N.isOpenMap_mkQ.map_nhds_eq (x := g) continuous_quot_mk.continuousAt]
  infer_instance

scoped instance cohomologyComplete : CompleteSpace DeningerMeyerStrongLogCohomology := by
  change @CompleteSpace DeningerMeyerStrongLogCohomology
    (IsTopologicalAddGroup.rightUniformSpace _)
  rw [IsTopologicalAddGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace]
  exact QuotientAddGroup.completeSpace_left DeningerMeyerStrongLogTarget
    (LinearMap.range deningerMeyerStrongLogSumLM).toAddSubgroup

scoped instance cohomologyCountablyGenerated :
    (𝓤 DeningerMeyerStrongLogCohomology).IsCountablyGenerated := by
  rw [uniformity_eq_comap_nhds_zero]
  infer_instance

scoped instance cohomologyCompletelyMetrizable :
    IsCompletelyPseudoMetrizableSpace DeningerMeyerStrongLogCohomology := by
  infer_instance

end DeningerMeyerNaturalTopology

open scoped DeningerMeyerNaturalTopology

/-- Exactness persists under natural source limits. -/
theorem deningerMeyerStrongLog_boundary_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (f : ι → DeningerMeyerCap) (g : DeningerMeyerStrongLogTarget)
    (h : Tendsto (fun i => deningerMeyerStrongLogSumLM (f i)) l (𝓝 g)) :
    ∃ f₀ : DeningerMeyerCap, deningerMeyerStrongLogSumLM f₀ = g :=
  deningerMeyerStrongLogSum_range_isClosed.mem_of_tendsto h
    (Eventually.of_forall fun i => Set.mem_range_self (f i))

end
end RHTower
