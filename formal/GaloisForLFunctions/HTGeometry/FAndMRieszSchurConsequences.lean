import GaloisForLFunctions.HTGeometry.FAndMRieszVanishing
import GaloisForLFunctions.HTGeometry.SingularSchurDefectCollapse

/-!
# Unconditional singular Schur double-boundary law

F. and M. Riesz discharges the one-sided Fourier-density hypothesis in the existing cofinal Schur
defect and Bernstein--Szego approximation package.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every singular infinite-support circle probability satisfies the complete cofinal Schur defect
collapse and canonical Bernstein--Szego approximation package. -/
theorem singularSchurDefect_doubleBoundary
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (hsing : (mu : Measure Circle) ⟂ₘ circleLebesgue) :
    HasSingularSchurDefectCollapse (mu : Measure Circle) hmu ∧
      HasBernsteinSzegoCofinalApproximation mu hmu :=
  singularSchurDefect_doubleBoundary_of_rieszBrothers mu hmu hsing
    (hasRieszBrothersDensityConclusion_of_fAndMRieszVanishing (mu : Measure Circle)
      (hasFAndMRieszVanishingConclusion_circle (mu : Measure Circle)))

end
end GaloisForLFunctions.HTGeometry
