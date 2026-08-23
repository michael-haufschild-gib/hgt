import GaloisForLFunctions.HTGeometry.CompletionDefectExactnessFlag

/-!
# Pointwise construction of provenance-continuous completion

The mixed lower--Scott topology on exactness flags was defined by generators.  This file removes
the remaining abstract-topology gap: convergence is equivalent to two explicit eventual tests for
every framed vector.

* every vector absent from the limiting boundary is eventually absent from stage boundaries;
* every vector present in the limiting cycle space is eventually present in stage cycle spaces.

These are the concrete obligations a source-level finite completion must prove.  They also expose
circular constructions: inserting a proposed limiting defect into every stage boundary violates
the first obligation exactly when that defect survives in the limit.
-/

open Set Topology TopologicalSpace

namespace GaloisForLFunctions.HTGeometry
namespace ExFlag

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Pointwise negative-boundary and positive-cycle obligations for completion of exactness flags. -/
def ProvenanceCompletionObligations
    {ι : Type*} (l : Filter ι) (stage : ι → ExFlag R M) (physical : ExFlag R M) : Prop :=
  (∀ v : M, v ∉ physical.boundary → ∀ᶠ i in l, v ∉ (stage i).boundary) ∧
  (∀ v : M, v ∈ physical.cycle → ∀ᶠ i in l, v ∈ (stage i).cycle)

/-- Provenance convergence is exactly the two pointwise source obligations. -/
theorem tendsto_iff_provenanceCompletionObligations
    {ι : Type*} {l : Filter ι} (stage : ι → ExFlag R M) (physical : ExFlag R M) :
    Filter.Tendsto stage l (nhds physical) ↔
      ProvenanceCompletionObligations l stage physical := by
  change Filter.Tendsto stage l
      (@nhds (ExFlag R M) (generateFrom (provSubbasis R M)) physical) ↔ _
  rw [TopologicalSpace.tendsto_nhds_generateFrom_iff]
  constructor
  · intro h
    constructor
    · intro v hv
      have hs := h (boundaryTest (R := R) (M := M) v)
        (Or.inl ⟨v, rfl⟩) hv
      change {i | v ∉ (stage i).boundary} ∈ l
      simpa [boundaryTest] using hs
    · intro v hv
      have hs := h (cycleTest (R := R) (M := M) v)
        (Or.inr ⟨v, rfl⟩) hv
      change {i | v ∈ (stage i).cycle} ∈ l
      simpa [cycleTest] using hs
  · rintro ⟨hb, hc⟩ s (⟨v, rfl⟩ | ⟨v, rfl⟩) hphysical
    · change {i | v ∉ (stage i).boundary} ∈ l
      exact hb v hphysical
    · change {i | v ∈ (stage i).cycle} ∈ l
      exact hc v hphysical

/-- A provenance-continuous completion of eventually exact source stages. -/
structure ExactCompletionDiagram
    (k W ι : Type*) [Field k] [AddCommGroup W] [Module k W]
    (l : Filter ι) (physical : ExFlag k W) where
  /-- Finite or regulated source stages in one marked ambient module. -/
  stage : ι → ExFlag k W
  /-- Source stages converge in the mixed provenance topology. -/
  converges : Filter.Tendsto stage l (nhds physical)
  /-- Exactness holds eventually before completion. -/
  eventually_exact : ∀ᶠ i in l,
    stage i ∈ BoundaryMigration.exactFlagLocus

/-- Provenance-continuous completion cannot create homology from eventually exact stages. -/
theorem ExactCompletionDiagram.physical_exact
    {k W ι : Type*} [Field k] [AddCommGroup W] [Module k W]
    {l : Filter ι} [l.NeBot] {physical : ExFlag k W}
    (D : ExactCompletionDiagram k W ι l physical) :
    physical.boundary = physical.cycle := by
  exact (BoundaryMigration.mem_exactFlagLocus_iff physical).1
    (BoundaryMigration.mem_exactFlagLocus_of_tendsto D.converges D.eventually_exact)

end ExFlag
end GaloisForLFunctions.HTGeometry
