import GaloisForLFunctions.HTGeometry.CriticalBlockFieldNormalization
import GaloisForLFunctions.HTGeometry.CriticalObservationComplexPoints
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumFiniteProper
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumIntegralSurjective

/-!
# Complex points of the critical block normalization

The finite normalization attached to a critical block has a canonical map to the exact
observation chart.  On complex points this map is continuous, proper, and surjective.  These are
the global topological inputs for the remaining local unramified-cover argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- Contravariant map on complex points induced by the critical block normalization. -/
def criticalBlockNormalizationProjection
    (B : Set (criticalGeometricSheet ℂ m n)) :
    AlgSpec (CriticalBlockNormalization ℂ B) →
      AlgSpec (criticalObservationChartRing ℂ m n) :=
  AlgSpec.precomp (IsScalarTower.toAlgHom ℂ
    (criticalObservationChartRing ℂ m n) (CriticalBlockNormalization ℂ B))

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- The critical block normalization projection is continuous. -/
theorem continuous_criticalBlockNormalizationProjection
    (B : Set (criticalGeometricSheet ℂ m n)) :
    Continuous (criticalBlockNormalizationProjection B) :=
  AlgSpec.continuous_precomp _

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- The critical block normalization projection is proper. -/
theorem isProperMap_criticalBlockNormalizationProjection
    (B : Set (criticalGeometricSheet ℂ m n)) :
    IsProperMap (criticalBlockNormalizationProjection B) := by
  exact AlgSpec.isProperMap_precomp_of_finite

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- Every complex point of the observation chart lifts to the critical block normalization. -/
theorem surjective_criticalBlockNormalizationProjection
    (B : Set (criticalGeometricSheet ℂ m n)) :
    Function.Surjective (criticalBlockNormalizationProjection B) := by
  exact AlgSpec.surjective_precomp_of_isIntegral

end

end GaloisForLFunctions.HTGeometry
