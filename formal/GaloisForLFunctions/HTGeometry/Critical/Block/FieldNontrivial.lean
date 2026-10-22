import GaloisForLFunctions.HTGeometry.Critical.Block.FieldNormalization
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyTransitive

/-!
# Nontriviality of a proper critical block field

A proper set of sheets containing the canonical sheet cannot be stabilized by every normal-closure
automorphism, because that action is transitive.  Finite Galois correspondence then says that its
stabilizer fixed field is a nontrivial extension of the observation field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The stabilizer of a proper set containing the canonical sheet is a proper subgroup of the
normal-closure Galois group. -/
theorem criticalBlockStabilizer_ne_top_of_mem_of_ne_univ
    {B : Set (criticalGeometricSheet K m n)}
    (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)
    (hne : B ≠ Set.univ) :
    criticalBlockStabilizer K B ≠ ⊤ := by
  intro htop
  apply hne
  rw [Set.eq_univ_iff_forall]
  intro y
  obtain ⟨σ, hσ⟩ := criticalNormalClosureAction_transitive K Fact.out Fact.out
    (criticalSourceNormalClosureEmbedding K m n) y
  have hσmem : σ ∈ criticalBlockStabilizer K B := by
    rw [htop]
    trivial
  change criticalNormalClosureAction K m n σ • B = B at hσmem
  have hy : criticalNormalClosureAction K m n σ •
      criticalSourceNormalClosureEmbedding K m n ∈
      criticalNormalClosureAction K m n σ • B :=
    Set.smul_mem_smul_set hmem
  change criticalNormalClosureAction K m n σ
      (criticalSourceNormalClosureEmbedding K m n) ∈
      criticalNormalClosureAction K m n σ • B at hy
  rw [hσ, hσmem] at hy
  exact hy

/-- **A proper block gives a nontrivial block cover.**  Its fixed field is strictly larger than the
observation field. -/
theorem criticalBlockFixedField_ne_bot_of_mem_of_ne_univ
    {B : Set (criticalGeometricSheet K m n)}
    (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)
    (hne : B ≠ Set.univ) :
    CriticalBlockFixedField K B ≠ ⊥ := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K Fact.out Fact.out
  letI : IsGalois (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_isGalois K Fact.out Fact.out
  intro hfix
  apply criticalBlockStabilizer_ne_top_of_mem_of_ne_univ K hmem hne
  apply fixedField_injective
  change IntermediateField.fixedField (criticalBlockStabilizer K B) = ⊥ at hfix
  rw [hfix, IsGalois.fixedField_top]

end

end GaloisForLFunctions.HTGeometry
