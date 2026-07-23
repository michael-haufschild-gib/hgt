import GaloisForLFunctions.RHTower.PrimeArchBernsteinPuritySourceEndpoint
import GaloisForLFunctions.RHTower.SoninCoupledBernsteinMismatchRH
import GaloisForLFunctions.RHTower.SoninCoupledNormalizedDeterminantCollar
import GaloisForLFunctions.RHTower.XiPrimeArchThermalEndpointUniversalityLaw

/-!
# Prime--arch thermal--Sonin determinant endpoint universality

The rectangular prime--polar source endpoint, the endpoint Bernstein-purity growth law, and every
nondegenerate coupled-Sonin relative determinant carry one exact phase.  Adjoining all Sonin
apertures to the existing thirty-one-chart thermal endpoint certificate therefore changes neither
its source classifier nor its RH content.
-/

open Filter Topology

namespace RHTower

noncomputable section

private theorem unitCollarExponentialEnvelope_of_subexponential
    {E : ℕ → ℝ} (h : SubexponentialSquareEnergyAtNatInfinity E) :
    UnitCollarExponentialEnvelope E := by
  intro ε hε
  let r : ℝ := 1 + ε
  have hr : 1 < r := by simp only [r]; linarith
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have htendsto := h r hr
  have hbdd : BddAbove (Set.range fun n : ℕ => E n / r ^ n) :=
    htendsto.isBoundedUnder_le.bddAbove_range
  obtain ⟨C₀, hC₀⟩ := hbdd
  refine ⟨max 1 C₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun n => ?_⟩
  have hpow : 0 < r ^ n := pow_pos hr0 n
  have hratio : E n / r ^ n ≤ max 1 C₀ :=
    (hC₀ ⟨n, rfl⟩).trans (le_max_right _ _)
  simpa only [r] using (div_le_iff₀ hpow).mp hratio

/-- **Prime-source/Sonin determinant law.**  For every admissible rectangular source and every
nondegenerate Sonin aperture, the critical source abscissa bound is equivalent to arbitrarily
thin exponential collars for the relative determinant's Bernstein purity. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_soninRelativeDeterminant_unitCollar
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (a : SoninCoupledNondegenerateAperture) :
    (LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal)) ↔
      UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) := by
  refine (primeArchBernsteinPurity_sourceEndpoint_iff hL hN).trans ⟨?_, ?_⟩
  · intro hsub
    apply (primeArchEndpoint_unitCollarEnvelope_iff_relativeDeterminantPurity a).1
    exact unitCollarExponentialEnvelope_of_subexponential hsub
  · intro hcollar
    apply subexponentialSquareEnergyAtNatInfinity_of_unitCollarExponentialEnvelope
      (E := primeArchEndpointBernsteinPurity)
    · intro n
      simpa only [primeArchEndpointBernsteinPurity] using
        bernsteinCoefficientPurity_nonneg
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n
    · exact (primeArchEndpoint_unitCollarEnvelope_iff_relativeDeterminantPurity a).2 hcollar

/-- Existing thermal endpoint certificate enlarged by the determinant collar for every
nondegenerate coupled-Sonin aperture. -/
def XiPrimeArchThermalSoninEndpointUniversalCertificate : Prop :=
  XiPrimeArchThermalEndpointUniversalCertificate ∧
    ∀ a : SoninCoupledNondegenerateAperture,
      UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n)

/-- **Thermal--Sonin endpoint universality law.**  For every admissible rectangular source, its
critical abscissa bound is equivalent to simultaneous realization of all existing thermal charts
and all nondegenerate coupled-Sonin determinant collars. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalSoninEndpointCertificate
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal)) ↔
      XiPrimeArchThermalSoninEndpointUniversalCertificate := by
  constructor
  · intro hsource
    refine ⟨
      (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_endpointUniversalCertificate
        hL hN).1 hsource, ?_⟩
    intro a
    exact
      (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_soninRelativeDeterminant_unitCollar
        hL hN a).1 hsource
  · intro hcertificate
    exact
      (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_endpointUniversalCertificate
        hL hN).2 hcertificate.1

end

end RHTower
