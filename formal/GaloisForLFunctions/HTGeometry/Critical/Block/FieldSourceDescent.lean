import GaloisForLFunctions.HTGeometry.Critical.Block.FieldUnramified
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Geometric.FieldPrimitivity
import GaloisForLFunctions.HTGeometry.HorizonGaloisAssignment

/-!
# Descent of a canonical-sheet block field into the critical source field

If a monodromy block contains the canonical source sheet, every automorphism fixing that sheet also
stabilizes the block.  The order reversal in finite Galois correspondence therefore places the
block-stabilizer fixed field inside the canonical embedded source field.  This realizes the block
field in the source where the two Kummer valuations live.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Pointwise

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)]

/-- **A block field whose block contains the canonical sheet embeds in the actual source field.** -/
theorem criticalBlockFixedField_le_sourceFieldRange_of_mem
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B) :
    IntermediateField.fixedField (criticalBlockStabilizer K B) ≤
      (criticalSourceNormalClosureEmbedding K m n).fieldRange := by
  have hsub :
      (criticalSourceNormalClosureEmbedding K m n).fieldRange.fixingSubgroup ≤
        criticalBlockStabilizer K B := by
    rw [criticalSourceNormalClosureFieldRange_fixingSubgroup_eq_actionStabilizer]
    intro g hg
    change criticalNormalClosureAction K m n g •
      criticalSourceNormalClosureEmbedding K m n =
        criticalSourceNormalClosureEmbedding K m n at hg
    change criticalNormalClosureAction K m n g • B = B
    let gG : criticalGeometricMonodromy K m n :=
      ⟨criticalNormalClosureAction K m n g, ⟨g, rfl⟩⟩
    rcases hB.smul_eq_or_disjoint gG with heq | hdisj
    · exact heq
    · exfalso
      have hx : criticalNormalClosureAction K m n g •
          criticalSourceNormalClosureEmbedding K m n ∈
          criticalNormalClosureAction K m n g • B :=
        Set.smul_mem_smul_set hmem
      rw [hg] at hx
      exact (Set.disjoint_left.1 hdisj hx) hmem
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K Fact.out Fact.out
  letI : IsGalois (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_isGalois K Fact.out Fact.out
  have hfix := fixedField_antitone hsub
  rw [IsGalois.fixedField_fixingSubgroup] at hfix
  exact hfix

end

end GaloisForLFunctions.HTGeometry
