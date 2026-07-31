import GaloisForLFunctions.RHTower.CompletedSeamCompactThorinExponentCapstone
import GaloisForLFunctions.RHTower.PrimeArchXiCompactThorinRH
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-!
# Rigidity of the completed-seam compact Thorin carrier

The compact Thorin RH interface asks for a finite positive compactly supported measure whose
logarithmic exponent agrees locally with the normalized completed Cassini source.  Such a carrier,
if it exists, is not an auxiliary choice: the exponent germ fixes every one of its moments, and
compact moment determinacy then fixes the measure itself.

This applies the general compact-carrier determinacy theorem from `HTGeometry` to the exact
completed-seam source.  No zero location, RH assumption, or numerical input is used.
-/

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

noncomputable section

/-- A specified measure and radius witness the completed-seam compact Thorin interface. -/
def IsPrimeArchCompactThorinWitness (μ : Measure ℝ) (B : ℝ) : Prop :=
  IsFiniteMeasure μ ∧
  0 < B ∧
  (∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ B) ∧
  completedSeamSourceLogExponent =ᶠ[𝓝 0] compactThorinExponent μ

theorem primeArchCompactThorinExponentRepresentation_iff_exists_witness :
    PrimeArchCompactThorinExponentRepresentation ↔
      ∃ (μ : Measure ℝ) (B : ℝ), IsPrimeArchCompactThorinWitness μ B := by
  rfl

/-- The exact exponent germ fixes every moment of a specified compact Thorin witness. -/
theorem IsPrimeArchCompactThorinWitness.normalizedPrimeArchMoment_eq_integral_pow
    {μ : Measure ℝ} {B : ℝ}
    (hμ : IsPrimeArchCompactThorinWitness μ B) (n : ℕ) :
    normalizedPrimeArchMoment n = ∫ x : ℝ, x ^ n ∂μ := by
  rcases hμ with ⟨hfinite, hB, hsupport, hexponent⟩
  letI : IsFiniteMeasure μ := hfinite
  have hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B :=
    hsupport.mono fun _ hx => hx.2
  have hdisk : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 / (2 * B) :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds
      (by simpa using (show (0 : ℝ) < 1 / (2 * B) by positivity))
  have hthorin : deriv (compactThorinExponent μ) =ᶠ[𝓝 0]
      compactMarkovTransform μ := by
    filter_upwards [hdisk] with z hz
    exact (hasDerivAt_compactThorinExponent μ hB hbound hz).deriv
  have hgerm : completedSeamMomentGerm =ᶠ[𝓝 0]
      compactMarkovTransform μ :=
    deriv_completedSeamSourceLogExponent_eventuallyEq_momentGerm.symm.trans
      (hexponent.deriv.trans hthorin)
  have hder := hgerm.iteratedDeriv_eq n
  rw [iteratedDeriv_completedSeamMomentGerm,
    iteratedDeriv_compactMarkovTransform μ hB hbound n
      (by simpa using (show (0 : ℝ) < 1 / (2 * B) by positivity)),
    compactMarkovKernelMoment_zero_node] at hder
  have hintc : (∫ x : ℝ, (x : ℂ) ^ n ∂μ) =
      ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) := by
    simpa using (integral_ofReal (X := ℝ) (μ := μ) (𝕜 := ℂ)
      (f := fun x : ℝ => x ^ n))
  rw [hintc] at hder
  have hfacne : (((Nat.factorial n : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact Complex.ofReal_inj.mp (mul_left_cancel₀ hfacne hder)

/-- Every real power is integrable against a compact Thorin witness. -/
theorem IsPrimeArchCompactThorinWitness.integrable_pow
    {μ : Measure ℝ} {B : ℝ}
    (hμ : IsPrimeArchCompactThorinWitness μ B) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) μ := by
  rcases hμ with ⟨hfinite, _hB, hsupport, _hexponent⟩
  letI : IsFiniteMeasure μ := hfinite
  have hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B :=
    hsupport.mono fun _ hx => hx.2
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ n) μ :=
    (continuous_id.pow n).aestronglyMeasurable
  refine Integrable.of_bound hmeas (B ^ n) ?_
  filter_upwards [hbound] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) hx n

/-- A compact Thorin witness is carried by its stated symmetric compact interval. -/
theorem IsPrimeArchCompactThorinWitness.measure_compl_Icc_eq_zero
    {μ : Measure ℝ} {B : ℝ}
    (hμ : IsPrimeArchCompactThorinWitness μ B) :
    μ (Set.Icc (-B) B)ᶜ = 0 := by
  rcases hμ with ⟨_hfinite, _hB, hsupport, _hexponent⟩
  have hmem : ∀ᵐ x : ℝ ∂μ, x ∈ Set.Icc (-B) B := by
    filter_upwards [hsupport] with x hx
    simpa only [Set.mem_Icc, abs_le] using hx.2
  exact mem_ae_iff.mp hmem

/-- **Completed-seam Thorin rigidity.** Two compact positive measures producing the exact
completed Cassini exponent germ are equal, even when supplied with different support radii. -/
theorem primeArchCompactThorinWitness_measure_unique
    {μ ν : Measure ℝ} {B C : ℝ}
    (hμ : IsPrimeArchCompactThorinWitness μ B)
    (hν : IsPrimeArchCompactThorinWitness ν C) :
    μ = ν := by
  rcases hμ with ⟨hfiniteμ, hB, hsupportμ, hexponentμ⟩
  rcases hν with ⟨hfiniteν, hC, hsupportν, hexponentν⟩
  letI : IsFiniteMeasure μ := hfiniteμ
  letI : IsFiniteMeasure ν := hfiniteν
  let hμ' : IsPrimeArchCompactThorinWitness μ B :=
    ⟨hfiniteμ, hB, hsupportμ, hexponentμ⟩
  let hν' : IsPrimeArchCompactThorinWitness ν C :=
    ⟨hfiniteν, hC, hsupportν, hexponentν⟩
  have hcarμ : μ (Set.Icc ((0 : ℝ) - B) (0 + B))ᶜ = 0 := by
    simpa using hμ'.measure_compl_Icc_eq_zero
  exact HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := normalizedPrimeArchMoment) hB hcarμ
    hμ'.normalizedPrimeArchMoment_eq_integral_pow hμ'.integrable_pow
    hν'.normalizedPrimeArchMoment_eq_integral_pow hν'.integrable_pow

/-- **Canonical-carrier classification.** Every compact Thorin witness is the canonical atomic
Xi-divisor pushforward measure.  Hence a source-side construction cannot choose a different
positive carrier: it must reconstruct this exact measure without assuming its zero locations. -/
theorem IsPrimeArchCompactThorinWitness.eq_primeArchXiCompactMomentMeasure
    {μ : Measure ℝ} {B : ℝ}
    (hμ : IsPrimeArchCompactThorinWitness μ B) :
    μ = primeArchXiCompactMomentMeasure := by
  letI : IsFiniteMeasure μ := hμ.1
  letI : IsFiniteMeasure primeArchXiCompactMomentMeasure :=
    primeArchXiCompactMomentMeasure_finite
  have hrep : PrimeArchCompactThorinExponentRepresentation :=
    primeArchCompactThorinExponentRepresentation_iff_exists_witness.mpr
      ⟨μ, B, hμ⟩
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_primeArchCompactThorinExponentRepresentation hrep
  have hcarμ : μ (Set.Icc ((0 : ℝ) - B) (0 + B))ᶜ = 0 := by
    simpa using hμ.measure_compl_Icc_eq_zero
  exact HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := normalizedPrimeArchMoment) hμ.2.1 hcarμ
    hμ.normalizedPrimeArchMoment_eq_integral_pow hμ.integrable_pow
    (fun n =>
      (integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis
        hRH n).symm)
    integrable_primeArchXiCompactMomentMeasure

end

end RHTower
