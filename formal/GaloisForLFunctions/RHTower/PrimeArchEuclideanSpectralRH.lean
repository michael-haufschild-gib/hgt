import GaloisForLFunctions.HTGeometry.EuclideanSpectralHankelStrict
import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH

/-!
# Euclidean spectral representation of the prime--Gamma source implies RH

This module exposes a quantum-field-theoretic source interface.  If the complete normalized
prime--archimedean moment tower is the integer-clock sampling of one positive Euclidean spectral
measure with infinite support, pushing that measure through `E ↦ exp (-tau E)` gives the existing
infinite-support moment representation and hence proves RH.

No spectral measure is postulated as an axiom.  The theorem is an unconditional implication and
isolates construction of that source-defined positive measure as the analytic research task.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- A positive infinite Euclidean spectrum represents every normalized prime--Gamma source
moment at one fixed nonzero clock spacing. -/
def PrimeArchEuclideanSpectralRepresentation : Prop :=
  ∃ (mu : Measure ℝ) (tau : ℝ),
    tau ≠ 0 ∧
    (∀ n, normalizedPrimeArchMoment n =
      HTGeometry.euclideanSpectralMoments mu tau n) ∧
    (∀ n, Integrable
      (fun energy ↦ HTGeometry.euclideanSpectralNode tau energy ^ n) mu) ∧
    (∀ F : Finset ℝ, 0 < mu {energy : ℝ | energy ∉ F})

/-- Euclidean spectral data push forward to the ordinary infinite-support moment interface already
consumed by the source Hankel criterion. -/
theorem primeArchInfiniteSupportMomentRepresentation_of_euclideanSpectral
    (hrep : PrimeArchEuclideanSpectralRepresentation) :
    PrimeArchInfiniteSupportMomentRepresentation := by
  obtain ⟨mu, tau, htau, hmom, hint, hmuinf⟩ := hrep
  let nu : Measure ℝ :=
    HTGeometry.observablePushforwardMeasure mu
      (HTGeometry.euclideanSpectralNode tau)
  refine ⟨nu, ?_, ?_, ?_⟩
  · intro n
    rw [hmom n, show nu = HTGeometry.observablePushforwardMeasure mu
      (HTGeometry.euclideanSpectralNode tau) by rfl]
    exact HTGeometry.euclideanSpectralMoments_eq_pushforward_moment mu tau n
  · intro n
    exact HTGeometry.integrable_pow_observablePushforwardMeasure mu (by fun_prop) (hint n)
  · intro F
    exact HTGeometry.observablePushforwardMeasure_infiniteSupport mu (by fun_prop)
      (HTGeometry.euclideanSpectralNode_infiniteSupport htau hmuinf) F

/-- The Euclidean spectral source interface supplies every strict prime--Gamma Hankel determinant. -/
theorem primeArchSourceMomentHankelDeterminantsPositive_of_euclideanSpectral
    (hrep : PrimeArchEuclideanSpectralRepresentation) :
    PrimeArchSourceMomentHankelDeterminantsPositive :=
  primeArchSourceMomentHankelDeterminantsPositive_of_infiniteSupportRepresentation
    (primeArchInfiniteSupportMomentRepresentation_of_euclideanSpectral hrep)

/-- **Euclidean spectral RH capstone.**  Constructing one positive infinite-support Euclidean
spectral representation of the normalized prime--Gamma moments proves RH. -/
theorem riemannHypothesis_of_primeArchEuclideanSpectralRepresentation
    (hrep : PrimeArchEuclideanSpectralRepresentation) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchInfiniteSupportMomentRepresentation
    (primeArchInfiniteSupportMomentRepresentation_of_euclideanSpectral hrep)

end

end RHTower
