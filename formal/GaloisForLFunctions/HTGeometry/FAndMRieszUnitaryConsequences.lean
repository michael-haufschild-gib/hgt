import GaloisForLFunctions.HTGeometry.FAndMRieszVanishing
import GaloisForLFunctions.HTGeometry.PureSingularCarrierUnitary

/-!
# Unconditional canonical unitary frames for pure singular circle carriers

F. and M. Riesz discharges the one-sided Fourier-density hypothesis in the existing coherent
inverse-Cholesky unitary construction.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The stable coherent inverse-Cholesky rows of every pure singular infinite-support circle
carrier extend to an onto unitary from coefficient `ℓ²` onto carrier `L²`. -/
theorem exists_circleCanonicalCarrierUnitary
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue) :
    ∃ U : CoefficientL2 ≃ₗᵢ[ℂ] Lp ℂ 2 mu,
      ∀ n : ℕ, U (lp.single 2 n 1) = circleCoherentFramePolynomial mu hmu n :=
  exists_circleCanonicalCarrierUnitary_of_rieszBrothers mu hmu hsing
    (hasRieszBrothersDensityConclusion_of_fAndMRieszVanishing mu
      (hasFAndMRieszVanishingConclusion_circle mu))

end
end GaloisForLFunctions.HTGeometry
