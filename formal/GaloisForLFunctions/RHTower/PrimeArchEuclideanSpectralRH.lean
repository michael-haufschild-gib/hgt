import GaloisForLFunctions.HTGeometry.EuclideanSpectralHankelStrict
import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH

/-!
# Euclidean spectral representation of the prime--Gamma source implies RH

This module exposes a quantum-field-theoretic source interface.  If the complete normalized
prime--archimedean moment tower is the integer-clock sampling of one positive Euclidean spectral
measure, pushing that measure through `E ↦ exp (-tau E)` gives the existing positive moment
representation and hence proves RH.  Nonzero spacing and infinite energy support are needed only
for the stronger strict-determinant conclusion, not for RH.

No spectral measure is postulated as an axiom.  The theorem is an unconditional implication and
isolates construction of that source-defined positive measure as the analytic research task.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- A positive Euclidean spectrum represents every normalized prime--Gamma source moment at one
fixed clock spacing.  No support-size or spacing-nondegeneracy hypothesis is needed for RH. -/
def PrimeArchEuclideanSpectralRepresentation : Prop :=
  ∃ (mu : Measure ℝ) (tau : ℝ),
    (∀ n, normalizedPrimeArchMoment n =
      HTGeometry.euclideanSpectralMoments mu tau n) ∧
    ∀ n, Integrable
      (fun energy ↦ HTGeometry.euclideanSpectralNode tau energy ^ n) mu

/-- The stronger Euclidean spectral interface whose nonzero spacing preserves infinite support
and therefore supplies strict determinants in every degree. -/
def PrimeArchInfiniteEuclideanSpectralRepresentation : Prop :=
  ∃ (mu : Measure ℝ) (tau : ℝ),
    tau ≠ 0 ∧
    (∀ n, normalizedPrimeArchMoment n =
      HTGeometry.euclideanSpectralMoments mu tau n) ∧
    (∀ n, Integrable
      (fun energy ↦ HTGeometry.euclideanSpectralNode tau energy ^ n) mu) ∧
    (∀ F : Finset ℝ, 0 < mu {energy : ℝ | energy ∉ F})

/-- The strong spectral interface forgets to the weak one sufficient for RH. -/
theorem primeArchEuclideanSpectralRepresentation_of_infinite
    (hrep : PrimeArchInfiniteEuclideanSpectralRepresentation) :
    PrimeArchEuclideanSpectralRepresentation := by
  obtain ⟨mu, tau, _, hmom, hint, _⟩ := hrep
  exact ⟨mu, tau, hmom, hint⟩

/-- Arbitrary positive Euclidean spectral data push forward to the ordinary moment interface
already sufficient for RH. -/
theorem primeArchMomentRepresentation_of_euclideanSpectral
    (hrep : PrimeArchEuclideanSpectralRepresentation) :
    PrimeArchMomentRepresentation := by
  obtain ⟨mu, tau, hmom, hint⟩ := hrep
  let nu : Measure ℝ :=
    HTGeometry.observablePushforwardMeasure mu
      (HTGeometry.euclideanSpectralNode tau)
  refine ⟨nu, ?_, ?_⟩
  · intro n
    rw [hmom n, show nu = HTGeometry.observablePushforwardMeasure mu
      (HTGeometry.euclideanSpectralNode tau) by rfl]
    exact HTGeometry.euclideanSpectralMoments_eq_pushforward_moment mu tau n
  · intro n
    exact HTGeometry.integrable_pow_observablePushforwardMeasure mu
      (HTGeometry.euclideanSpectralNode_measurable tau) (hint n)

/-- Euclidean spectral data push forward to the ordinary infinite-support moment interface already
consumed by the source Hankel criterion. -/
theorem primeArchInfiniteSupportMomentRepresentation_of_euclideanSpectral
    (hrep : PrimeArchInfiniteEuclideanSpectralRepresentation) :
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
    exact HTGeometry.integrable_pow_observablePushforwardMeasure mu
      (HTGeometry.euclideanSpectralNode_measurable tau) (hint n)
  · intro F
    exact HTGeometry.observablePushforwardMeasure_infiniteSupport mu
      (HTGeometry.euclideanSpectralNode_measurable tau)
      (HTGeometry.euclideanSpectralNode_infiniteSupport htau hmuinf) F

/-- The Euclidean spectral source interface supplies every strict prime--Gamma Hankel determinant. -/
theorem primeArchSourceMomentHankelDeterminantsPositive_of_euclideanSpectral
    (hrep : PrimeArchInfiniteEuclideanSpectralRepresentation) :
    PrimeArchSourceMomentHankelDeterminantsPositive :=
  primeArchSourceMomentHankelDeterminantsPositive_of_infiniteSupportRepresentation
    (primeArchInfiniteSupportMomentRepresentation_of_euclideanSpectral hrep)

/-- **Euclidean spectral RH capstone.**  Constructing any positive Euclidean spectral
representation of the normalized prime--Gamma moments proves RH. -/
theorem riemannHypothesis_of_primeArchEuclideanSpectralRepresentation
    (hrep : PrimeArchEuclideanSpectralRepresentation) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchMomentRepresentation
    (primeArchMomentRepresentation_of_euclideanSpectral hrep)

end

end RHTower
