import GaloisForLFunctions.HTGeometry.AlgebraPointResidueField
import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationComplexPoints
import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering

/-!
# Finite-étale block normalizations are analytic coverings

This is the exact algebraic-to-topological interface in the hidden-block argument.  Once the
finite block normalization is proved étale over the observation chart, its map on complex points is
a local homeomorphism.  Existing finiteness makes that map proper, hence a genuine covering.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet ℂ m n)}

/-- A finite étale critical block normalization induces a covering of the exact observation
chart on complex points. -/
theorem isCoveringMap_criticalBlockNormalizationProjection_of_etale
    [Algebra.Etale (criticalObservationChartRing ℂ m n)
      (CriticalBlockNormalization ℂ B)] :
    IsCoveringMap (criticalBlockNormalizationProjection B) := by
  apply isCoveringMap_of_isProperMap_of_isLocalHomeomorph
  · change IsLocalHomeomorph
      (AlgSpec.algebraSpectrumProjection
        (A := criticalObservationChartRing ℂ m n)
        (B := CriticalBlockNormalization ℂ B))
    exact AlgSpec.isLocalHomeomorph_algebraSpectrumProjection_of_finiteEtale
  · exact isProperMap_criticalBlockNormalizationProjection B

end

end GaloisForLFunctions.HTGeometry
