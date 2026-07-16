import GaloisForLFunctions.HTGeometry.FAndMRieszVanishing
import GaloisForLFunctions.HTGeometry.RieszSingularSzegoCollapse

/-!
# Unconditional circle consequences of F. and M. Riesz

This module discharges the last classical one-sided Fourier-density hypothesis from the singular
circle carrier trichotomy.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The square-summable Riesz-brothers density conclusion holds for every finite circle measure. -/
theorem hasRieszBrothersDensityConclusion_circle
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    HasRieszBrothersDensityConclusion mu circleLebesgue :=
  hasRieszBrothersDensityConclusion_of_fAndMRieszVanishing mu
    (hasFAndMRieszVanishingConclusion_circle mu)

/-- A pure singular infinite-support circle carrier has saturated polynomial graph, complete
analytic monomials, collapsing least Gram eigenvalue, and divergent canonical inverse-Cholesky
frame coordinates. -/
theorem pureSingularCarrier_trichotomy
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue) :
    (linearGraphSubmodule finsuppCoefficientL2
        (polynomialSynthesisL2 mu)).topologicalClosure = ⊤ ∧
      (analyticMonomialSpan mu).topologicalClosure = ⊤ ∧
      Tendsto (fun N => leastEigenvalue (circleMeasureGramTower mu N)
        (circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N)) atTop (𝓝 0) ∧
      Tendsto (normalizedFrameDetRoot (circleMeasureCanonicalFrameTower mu hmu))
        atTop atTop ∧
      Tendsto (euclideanFrameOpNorm (circleMeasureCanonicalFrameTower mu hmu))
        atTop atTop :=
  pureSingularCarrier_trichotomy_of_fAndMRieszVanishing mu hmu hsing
    (hasFAndMRieszVanishingConclusion_circle mu)

end
end GaloisForLFunctions.HTGeometry
