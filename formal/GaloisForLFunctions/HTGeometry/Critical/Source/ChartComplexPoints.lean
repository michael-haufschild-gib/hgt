import GaloisForLFunctions.HTGeometry.Critical.Source.ChartLocalization
import GaloisForLFunctions.HTGeometry.MvPolynomialAwayComplexPoints

/-!
# The complex points of the critical source chart are path connected

The source chart is the principal open of one nonzero polynomial in the raw coordinates
(`CriticalSourceChartLocalization`), and the complex points of a principal open of affine space are
path connected (`MvPolynomialAwayComplexPoints`).  This is the global connectivity input for the
block/étale covering argument: every intermediate cover of the critical horizon receives a
continuous surjection from this space, hence is path connected as well.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)]

/-- **The complex points of the critical source chart are path connected.** -/
theorem pathConnectedSpace_algSpec_criticalSourceChartRing :
    PathConnectedSpace (AlgSpec (criticalSourceChartRing ℂ m n)) :=
  AlgSpec.pathConnectedSpace_algSpec_localizationAway _
    (criticalSourceChartPoly_ne_zero ℂ m n)

end

end GaloisForLFunctions.HTGeometry
