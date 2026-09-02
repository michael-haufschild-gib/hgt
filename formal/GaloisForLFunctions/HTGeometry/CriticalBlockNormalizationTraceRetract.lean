import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationTraceEvaluation

/-!
# Trace retraction for a critical block normalization

Normalized field trace is a left inverse to the inclusion of the block normalization into the
critical source chart. Consequently, flatness of the source chart over the observation chart
descends to every block normalization as a linear retract.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

/-- Multiplication by a positive natural and by its inverse ground-field scalar cancel. -/
theorem algebraMap_inv_natCast_mul_nsmul
    {K E : Type*} [Field K] [Field E] [CharZero E] [Algebra K E]
    (d : ℕ) (hd : 0 < d) (x : E) :
    algebraMap K E ((d : K)⁻¹) * (d • x) = x := by
  rw [map_inv₀, map_natCast, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)), one_mul]

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet K m n)}
variable (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
  (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)

/-- Normalized trace is a left inverse to the block-normalization chart inclusion. -/
theorem criticalBlockNormalizedTraceToNormalization_comp_toChart :
    (criticalBlockNormalizedTraceToNormalization K hB hmem).comp
        (blockNormalizationToChart K hB hmem).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  change (criticalBlockNormalizedTraceToNormalization K hB hmem
    (blockNormalizationToChart K hB hmem b)).1 = b.1
  rw [coe_criticalBlockNormalizedTraceToNormalization,
    criticalBlockNormalizedTraceToField_apply]
  rw [algebraMap_blockNormalizationToChart K hB hmem]
  rw [criticalBlockFieldTraceValue_blockNormalizationToSource]
  rw [Algebra.smul_def]
  rw [algebraMap_criticalBlockTraceDenominator]
  exact algebraMap_inv_natCast_mul_nsmul _
    (criticalBlockExtensionDegree_pos K hB hmem) b.1

include hB hmem in
/-- A flat critical source chart makes every canonical-sheet block normalization flat. -/
theorem criticalBlockNormalization_flat_of_sourceChart_flat
    [Module.Flat (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)] :
    Module.Flat (criticalObservationChartRing K m n) (CriticalBlockNormalization K B) := by
  exact Module.Flat.of_retract (blockNormalizationToChart K hB hmem).toLinearMap
    (criticalBlockNormalizedTraceToNormalization K hB hmem)
    (criticalBlockNormalizedTraceToNormalization_comp_toChart K hB hmem)

end

end GaloisForLFunctions.HTGeometry
