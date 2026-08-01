import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH
import GaloisForLFunctions.RHTower.PrimeArchXiCompactThorinRH
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-!
# Rigidity of unrestricted prime--archimedean moment carriers

An arbitrary positive measure representing all normalized prime--archimedean moments already
implies RH.  This file proves the stronger classification omitted by that implication: no support
assumption is needed to identify the measure.  RH supplies the canonical compact atomic Xi-divisor
measure, and existence of that one compact representative makes the whole Hamburger moment problem
determinate.  Every unrestricted positive witness is therefore the canonical divisor pushforward.

This removes alternative-carrier freedom from Route D.  It does not construct a witness or assume
RH; RH is derived from the supplied witness before canonical moment identities are used.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- A specified positive measure represents every normalized prime--archimedean moment.  No
support, compactness, or determinacy hypothesis is imposed. -/
def IsPrimeArchMomentWitness (μ : Measure ℝ) : Prop :=
  (∀ k, normalizedPrimeArchMoment k = ∫ x : ℝ, x ^ k ∂μ) ∧
    ∀ k, Integrable (fun x : ℝ => x ^ k) μ

/-- The existential unrestricted witness interface is exactly the existing moment representation. -/
theorem primeArchMomentRepresentation_iff_exists_witness :
    PrimeArchMomentRepresentation ↔ ∃ μ : Measure ℝ, IsPrimeArchMomentWitness μ := by
  rfl

/-- Integrability of the zeroth power makes every unrestricted witness a finite measure. -/
theorem IsPrimeArchMomentWitness.isFiniteMeasure
    {μ : Measure ℝ} (hμ : IsPrimeArchMomentWitness μ) :
    IsFiniteMeasure μ := by
  apply (integrable_const_iff_isFiniteMeasure
    (μ := μ) (c := (1 : ℝ)) one_ne_zero).mp
  simpa only [pow_zero] using hμ.2 0

/-- A specified witness packages into the existing representation interface. -/
theorem IsPrimeArchMomentWitness.toRepresentation
    {μ : Measure ℝ} (hμ : IsPrimeArchMomentWitness μ) :
    PrimeArchMomentRepresentation :=
  ⟨μ, hμ.1, hμ.2⟩

/-- The canonical Xi-divisor measure is carried by the symmetric interval used for compact moment
determinacy. -/
theorem primeArchXiCompactMomentMeasure_measure_compl_Icc_negOne_one_eq_zero :
    primeArchXiCompactMomentMeasure
      (Set.Icc ((0 : ℝ) - 1) (0 + 1))ᶜ = 0 := by
  apply mem_ae_iff.mp
  filter_upwards [ae_primeArchXiCompactMomentMeasure_mem_zero_one] with x hx
  simpa [Set.mem_Icc, abs_le] using hx.2

/-- **Unrestricted-carrier rigidity.**  Every positive measure representing the full Route D
moment tower is the canonical compact atomic Xi-divisor pushforward, even when the supplied measure
has no support bound. -/
theorem IsPrimeArchMomentWitness.eq_primeArchXiCompactMomentMeasure
    {μ : Measure ℝ} (hμ : IsPrimeArchMomentWitness μ) :
    μ = primeArchXiCompactMomentMeasure := by
  letI : IsFiniteMeasure μ := hμ.isFiniteMeasure
  letI : IsFiniteMeasure primeArchXiCompactMomentMeasure :=
    primeArchXiCompactMomentMeasure_finite
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_primeArchMomentRepresentation hμ.toRepresentation
  have heq := HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := normalizedPrimeArchMoment)
    (mu := primeArchXiCompactMomentMeasure) (nu := μ)
    (c := 0) (r := 1) (by norm_num : (0 : ℝ) < 1)
    primeArchXiCompactMomentMeasure_measure_compl_Icc_negOne_one_eq_zero
    (fun k =>
      (integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis hRH k).symm)
    integrable_primeArchXiCompactMomentMeasure hμ.1 hμ.2
  exact heq.symm

/-- Every unrestricted witness is automatically carried by the sharp canonical source aperture
`[0, 2/41]`. -/
theorem IsPrimeArchMomentWitness.ae_mem_zero_two_over_fortyOne
    {μ : Measure ℝ} (hμ : IsPrimeArchMomentWitness μ) :
    ∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ 2 / 41 := by
  rw [hμ.eq_primeArchXiCompactMomentMeasure]
  exact ae_primeArchXiCompactMomentMeasure_mem_zero_two_over_fortyOne

/-- Two unrestricted positive Route D moment witnesses are equal. -/
theorem primeArchMomentWitness_unique
    {μ ν : Measure ℝ}
    (hμ : IsPrimeArchMomentWitness μ) (hν : IsPrimeArchMomentWitness ν) :
    μ = ν := by
  rw [hμ.eq_primeArchXiCompactMomentMeasure,
    hν.eq_primeArchXiCompactMomentMeasure]

/-- Every positive Euclidean spectral realization has the same observable pushforward: the
canonical Xi-divisor moment measure.  Energy-coordinate choices cannot change the Route D cyclic
spectral law. -/
theorem observablePushforwardMeasure_euclideanSpectralNode_eq_primeArchXiCompactMomentMeasure
    (μ : Measure ℝ) (tau : ℝ)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      HTGeometry.euclideanSpectralMoments μ tau n)
    (hint : ∀ n, Integrable
      (fun energy ↦ HTGeometry.euclideanSpectralNode tau energy ^ n) μ) :
    HTGeometry.observablePushforwardMeasure μ
        (HTGeometry.euclideanSpectralNode tau) =
      primeArchXiCompactMomentMeasure := by
  let ν : Measure ℝ :=
    HTGeometry.observablePushforwardMeasure μ
      (HTGeometry.euclideanSpectralNode tau)
  have hν : IsPrimeArchMomentWitness ν := by
    constructor
    · intro n
      rw [hmom n, show ν = HTGeometry.observablePushforwardMeasure μ
        (HTGeometry.euclideanSpectralNode tau) by rfl]
      exact HTGeometry.euclideanSpectralMoments_eq_pushforward_moment μ tau n
    · intro n
      exact HTGeometry.integrable_pow_observablePushforwardMeasure μ
        (HTGeometry.euclideanSpectralNode_measurable tau) (hint n)
  exact hν.eq_primeArchXiCompactMomentMeasure

/-- The canonical compact Xi measure represents the source moments exactly if and only if RH. -/
theorem isPrimeArchMomentWitness_primeArchXiCompactMomentMeasure_iff_riemannHypothesis :
    IsPrimeArchMomentWitness primeArchXiCompactMomentMeasure ↔ RiemannHypothesis := by
  constructor
  · intro hμ
    exact riemannHypothesis_of_primeArchMomentRepresentation hμ.toRepresentation
  · intro hRH
    exact ⟨fun k =>
      (integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis hRH k).symm,
      integrable_primeArchXiCompactMomentMeasure⟩

/-- **Unique-carrier classification.**  Unique existence of an unrestricted positive Route D
moment carrier is exactly RH.  When it exists, the witness is the canonical Xi-divisor measure. -/
theorem existsUnique_primeArchMomentWitness_iff_riemannHypothesis :
    (∃! μ : Measure ℝ, IsPrimeArchMomentWitness μ) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨μ, hμ, _⟩
    exact riemannHypothesis_of_primeArchMomentRepresentation hμ.toRepresentation
  · intro hRH
    refine ⟨primeArchXiCompactMomentMeasure, ?_, ?_⟩
    · exact isPrimeArchMomentWitness_primeArchXiCompactMomentMeasure_iff_riemannHypothesis.mpr hRH
    · intro μ hμ
      exact hμ.eq_primeArchXiCompactMomentMeasure

/-- Existence and unique existence coincide for the complete prime--archimedean moment tower. -/
theorem primeArchMomentRepresentation_iff_existsUnique_witness :
    PrimeArchMomentRepresentation ↔
      ∃! μ : Measure ℝ, IsPrimeArchMomentWitness μ := by
  rw [primeArchMomentRepresentation_iff_riemannHypothesis,
    existsUnique_primeArchMomentWitness_iff_riemannHypothesis]

end

end RHTower
