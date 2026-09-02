import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationTrace

/-!
# Coercion formula for the block-normalization trace

This leaf keeps the proof component of `LinearMap.codRestrict` opaque. Downstream calculations can
therefore expose the normalized field trace without normalizing its integrality certificate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet K m n)}
variable (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
  (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)

/-- Coercing the normalization-valued trace recovers its fixed-field-valued trace. -/
@[simp] theorem coe_criticalBlockNormalizedTraceToNormalization
    (s : criticalSourceChartRing K m n) :
    (criticalBlockNormalizedTraceToNormalization K hB hmem s :
      CriticalBlockFixedField K B) =
      criticalBlockNormalizedTraceToField K hB hmem s := by
  rfl

end

end GaloisForLFunctions.HTGeometry
