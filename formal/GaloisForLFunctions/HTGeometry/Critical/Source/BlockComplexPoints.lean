import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationChart
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationComplexPoints
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartComplexPoints
import GaloisForLFunctions.HTGeometry.Critical.Observation.ConnectedCover

/-!
# The source-chart lift of a critical block cover on complex points

A block normalization containing the canonical sheet embeds into the source chart.  Contravariance
therefore gives a canonical continuous map from source-chart complex points to block-normalization
complex points, and its composite with the block projection is exactly the source observation map.
This names the lift through which the two source meridians close.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet ℂ m n)}

/-- The finite critical source chart projected to the marked observation chart on complex points. -/
def criticalSourceChartProjection :
    AlgSpec (criticalSourceChartRing ℂ m n) →
      AlgSpec (criticalObservationChartRing ℂ m n) :=
  AlgSpec.precomp (IsScalarTower.toAlgHom ℂ
    (criticalObservationChartRing ℂ m n) (criticalSourceChartRing ℂ m n))

/-- The canonical source-chart lift to the block normalization on complex points. -/
def criticalSourceToBlockNormalization
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    AlgSpec (criticalSourceChartRing ℂ m n) →
      AlgSpec (CriticalBlockNormalization ℂ B) :=
  AlgSpec.precomp ((blockNormalizationToChart ℂ hB hmem).restrictScalars ℂ)

/-- The source-chart lift to the block normalization is continuous. -/
theorem continuous_criticalSourceToBlockNormalization
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    Continuous (criticalSourceToBlockNormalization hB hmem) :=
  AlgSpec.continuous_precomp _

/-- The block projection after the canonical source lift is exactly the source observation map. -/
theorem criticalBlockNormalizationProjection_comp_sourceToBlock
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    criticalBlockNormalizationProjection B ∘
        criticalSourceToBlockNormalization hB hmem =
      criticalSourceChartProjection := by
  funext chi
  apply AlgHom.ext
  intro a
  change chi (blockNormalizationToChart ℂ hB hmem
      (algebraMap (criticalObservationChartRing ℂ m n)
        (CriticalBlockNormalization ℂ B) a)) =
    chi (algebraMap (criticalObservationChartRing ℂ m n)
      (criticalSourceChartRing ℂ m n) a)
  rw [(blockNormalizationToChart ℂ hB hmem).commutes]

/-- The actual source chart projected to analytic torus-affine observation coordinates through a
block normalization. -/
def criticalSourceBlockAnalyticProjection
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    AlgSpec (criticalSourceChartRing ℂ m n) →
      ComplexTorusAffineChart (n + m - 2) :=
  criticalObservationAnalyticProjection m n
    (criticalBlockNormalizationProjection B) ∘
      criticalSourceToBlockNormalization hB hmem

/-- The source-to-block analytic projection is continuous. -/
theorem continuous_criticalSourceBlockAnalyticProjection
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    Continuous (criticalSourceBlockAnalyticProjection hB hmem) :=
  (criticalObservationComplexPointHomeomorph m n).continuous.comp
    ((continuous_criticalBlockNormalizationProjection B).comp
      (continuous_criticalSourceToBlockNormalization hB hmem))

/-- The source-to-block analytic projection as a bundled continuous map. -/
def criticalSourceBlockAnalyticProjectionContinuousMap
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    C(AlgSpec (criticalSourceChartRing ℂ m n),
      ComplexTorusAffineChart (n + m - 2)) :=
  ⟨criticalSourceBlockAnalyticProjection hB hmem,
    continuous_criticalSourceBlockAnalyticProjection hB hmem⟩

end

end GaloisForLFunctions.HTGeometry
