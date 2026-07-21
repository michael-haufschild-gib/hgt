import GaloisForLFunctions.HTGeometry.EuclideanSpectralHankelStrict
import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH
import GaloisForLFunctions.RHTower.PrimeArchThermalKrylovEquivalence

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

/-- Countable positive spectral measure whose atom at energy `-log lambda_j` has mass `lambda_j`,
where `lambda_j` is the positive real Xi thermal node. -/
def primeArchXiEuclideanSpectralMeasure : Measure ℝ :=
  Measure.sum fun j : ℕ =>
    ENNReal.ofReal (xiThermalNode (xiThermalEnumeration j)) •
      Measure.dirac (-Real.log (xiThermalNode (xiThermalEnumeration j)))

@[simp] theorem euclideanSpectralNode_one_neg_log_xiThermalNode (j : ℕ) :
    HTGeometry.euclideanSpectralNode 1
        (-Real.log (xiThermalNode (xiThermalEnumeration j))) =
      xiThermalNode (xiThermalEnumeration j) := by
  rw [HTGeometry.euclideanSpectralNode]
  rw [neg_mul_neg, one_mul]
  exact Real.exp_log (xiThermalNode_pos _)

/-- Every integer-clock power is integrable against the canonical countable Xi spectral measure. -/
theorem integrable_primeArchXiEuclideanSpectralMeasure (n : ℕ) :
    Integrable (fun energy => HTGeometry.euclideanSpectralNode 1 energy ^ n)
      primeArchXiEuclideanSpectralMeasure := by
  rw [primeArchXiEuclideanSpectralMeasure]
  apply integrable_sum_dirac (fun j => by simp [ENNReal.ofReal_ne_top])
  convert (hasSum_xiThermalEnumeration_positiveMoment n).summable using 1
  funext j
  rw [ENNReal.toReal_ofReal (xiThermalNode_pos _).le,
    euclideanSpectralNode_one_neg_log_xiThermalNode]
  simp only [Real.norm_eq_abs, abs_pow, abs_of_pos (xiThermalNode_pos _)]
  ring

/-- Under RH, integer-clock moments of the canonical positive Xi spectral measure are exactly the
normalized continued prime--Gamma moments. -/
theorem euclideanSpectralMoments_primeArchXiMeasure_eq_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    HTGeometry.euclideanSpectralMoments
        primeArchXiEuclideanSpectralMeasure 1 n =
      normalizedPrimeArchMoment n := by
  rw [HTGeometry.euclideanSpectralMoments,
    primeArchXiEuclideanSpectralMeasure,
    integral_sum_dirac (fun j => by simp [ENNReal.ofReal_ne_top])]
  calc
    (∑' j : ℕ,
        (ENNReal.ofReal (xiThermalNode (xiThermalEnumeration j))).toReal •
          HTGeometry.euclideanSpectralNode 1
            (-Real.log (xiThermalNode (xiThermalEnumeration j))) ^ n) =
        ∑' j : ℕ, xiThermalNode (xiThermalEnumeration j) ^ (n + 1) := by
      apply tsum_congr
      intro j
      rw [ENNReal.toReal_ofReal (xiThermalNode_pos _).le,
        euclideanSpectralNode_one_neg_log_xiThermalNode]
      simp only [smul_eq_mul]
      ring
    _ = normalizedPrimeArchMoment n :=
      (hasSum_xiThermalEnumeration_pow_of_rh hRH n).tsum_eq

/-- RH constructs the positive Euclidean spectral representation required by the existing
consumer, using the exact reciprocal-square Xi thermal atoms. -/
theorem primeArchEuclideanSpectralRepresentation_of_riemannHypothesis
    (hRH : RiemannHypothesis) : PrimeArchEuclideanSpectralRepresentation := by
  refine ⟨primeArchXiEuclideanSpectralMeasure, 1, ?_, ?_⟩
  · intro n
    exact (euclideanSpectralMoments_primeArchXiMeasure_eq_of_riemannHypothesis
      hRH n).symm
  · exact integrable_primeArchXiEuclideanSpectralMeasure

/-- Under RH, the canonical Xi energy measure itself has infinite support.  This is pulled back
from infinite support of its moment pushforward, which follows from strict positivity of the
canonical moment form. -/
theorem primeArchXiEuclideanSpectralMeasure_infiniteSupport_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∀ F : Finset ℝ,
      0 < primeArchXiEuclideanSpectralMeasure {energy : ℝ | energy ∉ F} := by
  let nu : Measure ℝ :=
    HTGeometry.observablePushforwardMeasure primeArchXiEuclideanSpectralMeasure
      (HTGeometry.euclideanSpectralNode 1)
  have hmom : ∀ k, normalizedPrimeArchMoment k = ∫ y, y ^ k ∂nu := by
    intro k
    rw [show nu = HTGeometry.observablePushforwardMeasure
      primeArchXiEuclideanSpectralMeasure
      (HTGeometry.euclideanSpectralNode 1) by rfl]
    rw [← HTGeometry.euclideanSpectralMoments_eq_pushforward_moment]
    exact (euclideanSpectralMoments_primeArchXiMeasure_eq_of_riemannHypothesis
      hRH k).symm
  have hint : ∀ k, Integrable (fun y : ℝ => y ^ k) nu := by
    intro k
    exact HTGeometry.integrable_pow_observablePushforwardMeasure
      primeArchXiEuclideanSpectralMeasure
      (HTGeometry.euclideanSpectralNode_measurable 1)
      (integrable_primeArchXiEuclideanSpectralMeasure k)
  have hnuinf : ∀ G : Finset ℝ, 0 < nu {y : ℝ | y ∉ G} := by
    intro G
    exact HTGeometry.measure_compl_finset_pos_of_positiveMomentForm
      (positiveMomentForm_normalizedPrimeArchMoment_of_riemannHypothesis hRH)
      hmom hint G
  exact HTGeometry.infiniteSupport_of_observablePushforwardMeasure
    primeArchXiEuclideanSpectralMeasure
    (HTGeometry.euclideanSpectralNode_measurable 1)
    (by simpa only [nu] using hnuinf)

/-- RH constructs the stronger nonzero-clock, infinite-support Euclidean spectral realization. -/
theorem primeArchInfiniteEuclideanSpectralRepresentation_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchInfiniteEuclideanSpectralRepresentation := by
  exact ⟨primeArchXiEuclideanSpectralMeasure, 1, one_ne_zero,
    fun n => (euclideanSpectralMoments_primeArchXiMeasure_eq_of_riemannHypothesis
      hRH n).symm,
    integrable_primeArchXiEuclideanSpectralMeasure,
    primeArchXiEuclideanSpectralMeasure_infiniteSupport_of_riemannHypothesis hRH⟩

/-- Even the infinite-support Euclidean spectral interface is exactly RH. -/
theorem primeArchInfiniteEuclideanSpectralRepresentation_iff_riemannHypothesis :
    PrimeArchInfiniteEuclideanSpectralRepresentation ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_primeArchEuclideanSpectralRepresentation
      (primeArchEuclideanSpectralRepresentation_of_infinite h)
  · exact primeArchInfiniteEuclideanSpectralRepresentation_of_riemannHypothesis

/-- Positive Euclidean spectral representability of the canonical source tower is exactly RH,
not a weaker independent producer assumption. -/
theorem primeArchEuclideanSpectralRepresentation_iff_riemannHypothesis :
    PrimeArchEuclideanSpectralRepresentation ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_primeArchEuclideanSpectralRepresentation
  · exact primeArchEuclideanSpectralRepresentation_of_riemannHypothesis

end

end RHTower
