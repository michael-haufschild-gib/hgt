import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationChart
import GaloisForLFunctions.HTGeometry.CriticalSourceChartComplexPoints
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumIntegralDescent

/-!
# The complex points of a block cover of the critical horizon are path connected

The block normalization embeds into the source chart ring over the observation chart
(`CriticalBlockNormalizationChart`), the source chart ring is integral over that chart, and the
complex points of the source chart are path connected because the chart is a principal open of
affine space.  Path connectedness therefore descends
(`AlgSpec.pathConnectedSpace_of_injective_integral`).

This is the global connectivity input the block/étale argument for full symmetric critical-horizon
monodromy consumes.
-/

namespace GaloisForLFunctions.HTGeometry

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet ℂ m n)}

/-- **The complex points of a block normalization of the critical horizon are path connected.** -/
theorem pathConnectedSpace_algSpec_criticalBlockNormalization
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    PathConnectedSpace (AlgSpec (CriticalBlockNormalization ℂ B)) := by
  haveI : PathConnectedSpace (AlgSpec (criticalSourceChartRing ℂ m n)) :=
    pathConnectedSpace_algSpec_criticalSourceChartRing m n
  have hinj : Function.Injective
      (((blockNormalizationToChart ℂ hB hmem).restrictScalars ℂ) :
        CriticalBlockNormalization ℂ B → criticalSourceChartRing ℂ m n) :=
    injective_blockNormalizationToChart ℂ hB hmem
  refine AlgSpec.pathConnectedSpace_of_injective_integral
    ((blockNormalizationToChart ℂ hB hmem).restrictScalars ℂ) hinj ?_
  intro b
  have hint : ∃ q : Polynomial (criticalObservationChartRing ℂ m n), q.Monic ∧
      Polynomial.eval₂ (algebraMap (criticalObservationChartRing ℂ m n)
        (criticalSourceChartRing ℂ m n)) b q = 0 :=
    Algebra.IsIntegral.isIntegral b
  obtain ⟨p, hp, hpe⟩ := hint
  refine ⟨p.map (algebraMap (criticalObservationChartRing ℂ m n)
    (CriticalBlockNormalization ℂ B)),
    hp.map (algebraMap (criticalObservationChartRing ℂ m n)
      (CriticalBlockNormalization ℂ B)), ?_⟩
  have hcomp : (((blockNormalizationToChart ℂ hB hmem).restrictScalars ℂ).toRingHom).comp
      (algebraMap (criticalObservationChartRing ℂ m n) (CriticalBlockNormalization ℂ B))
      = algebraMap (criticalObservationChartRing ℂ m n) (criticalSourceChartRing ℂ m n) :=
    RingHom.ext fun a => (blockNormalizationToChart ℂ hB hmem).commutes a
  rw [Polynomial.eval₂_map, hcomp]
  exact hpe

end GaloisForLFunctions.HTGeometry
