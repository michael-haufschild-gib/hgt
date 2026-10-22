import GaloisForLFunctions.HTGeometry.Critical.Block.FieldSourceDescent
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Block.FieldNormalization
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartObservationTower

/-!
# The block normalization sits inside the source chart

A monodromy block containing the canonical sheet has its fixed field inside the actual source field
(`criticalBlockFixedField_le_sourceFieldRange_of_mem`).  Its normalization over the observation
chart therefore consists of elements of the source field integral over that chart, and the source
chart is integrally closed with the source field as fraction field
(`exists_criticalSourceChart_of_isIntegral`).  So the block normalization embeds, over the
observation chart, into the source chart ring.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet K m n)}

/-- The block field, included into the range of the canonical source sheet. -/
def blockFieldInclusion
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B) :
    CriticalBlockFixedField K B →ₐ[criticalObservationField K m n]
      (criticalSourceNormalClosureEmbedding K m n).range :=
  AlgHom.codRestrict (IntermediateField.val (CriticalBlockFixedField K B))
    (criticalSourceNormalClosureEmbedding K m n).range
    (fun x => criticalBlockFixedField_le_sourceFieldRange_of_mem K hB hmem x.2)

/-- **The block field realised inside the actual critical source field.** -/
def blockFieldToSource
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B) :
    CriticalBlockFixedField K B →ₐ[criticalObservationField K m n]
      criticalSourceField K m n :=
  ((AlgEquiv.ofInjectiveField
      (criticalSourceNormalClosureEmbedding K m n)).symm.toAlgHom).comp
    (blockFieldInclusion K hB hmem)

variable (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
  (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)

/-- The block normalization, mapped into the actual source field over the observation chart. -/
def blockNormalizationToSource :
    CriticalBlockNormalization K B →ₐ[criticalObservationChartRing K m n]
      criticalSourceField K m n :=
  ((blockFieldToSource K hB hmem).restrictScalars (criticalObservationChartRing K m n)).comp
    (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) (CriticalBlockFixedField K B))

theorem isIntegral_blockNormalizationToSource (b : CriticalBlockNormalization K B) :
    IsIntegral (criticalObservationChartRing K m n)
      (blockNormalizationToSource K hB hmem b) := by
  have hb : IsIntegral (criticalObservationChartRing K m n)
      (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
        (CriticalBlockNormalization K B) (CriticalBlockFixedField K B) b) := b.2
  exact hb.map ((blockFieldToSource K hB hmem).restrictScalars
    (criticalObservationChartRing K m n))

theorem blockNormalizationToSource_mem_range (b : CriticalBlockNormalization K B) :
    blockNormalizationToSource K hB hmem b ∈
      (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n) (criticalSourceField K m n)).range := by
  obtain ⟨d, hd⟩ := exists_criticalSourceChart_of_isIntegral K
    (isIntegral_blockNormalizationToSource K hB hmem b)
  exact ⟨d, hd⟩

/-- **The block normalization sits inside the source chart ring.** -/
def blockNormalizationToChart :
    CriticalBlockNormalization K B →ₐ[criticalObservationChartRing K m n]
      criticalSourceChartRing K m n :=
  ((AlgEquiv.ofInjective
      (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n) (criticalSourceField K m n))
      (algebraMap_criticalSourceChartRing_injective K m n)).symm.toAlgHom).comp
    (AlgHom.codRestrict (blockNormalizationToSource K hB hmem) _
      (blockNormalizationToSource_mem_range K hB hmem))

theorem algebraMap_blockNormalizationToChart (b : CriticalBlockNormalization K B) :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (blockNormalizationToChart K hB hmem b) =
      blockNormalizationToSource K hB hmem b := by
  have hinj := algebraMap_criticalSourceChartRing_injective K m n
  have h := (AlgEquiv.ofInjective
      (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n) (criticalSourceField K m n)) hinj).apply_symm_apply
    ⟨blockNormalizationToSource K hB hmem b,
      blockNormalizationToSource_mem_range K hB hmem b⟩
  exact congrArg Subtype.val h

theorem injective_blockNormalizationToSource :
    Function.Injective (blockNormalizationToSource K hB hmem) := by
  intro x y hxy
  have h1 : blockFieldToSource K hB hmem
        (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
          (CriticalBlockNormalization K B) (CriticalBlockFixedField K B) x)
      = blockFieldToSource K hB hmem
        (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
          (CriticalBlockNormalization K B) (CriticalBlockFixedField K B) y) := hxy
  exact Subtype.ext ((blockFieldToSource K hB hmem).toRingHom.injective h1)

theorem injective_blockNormalizationToChart :
    Function.Injective (blockNormalizationToChart K hB hmem) := by
  intro x y hxy
  apply injective_blockNormalizationToSource K hB hmem
  have h := congrArg
    (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)) hxy
  rwa [algebraMap_blockNormalizationToChart, algebraMap_blockNormalizationToChart] at h

end

end GaloisForLFunctions.HTGeometry
