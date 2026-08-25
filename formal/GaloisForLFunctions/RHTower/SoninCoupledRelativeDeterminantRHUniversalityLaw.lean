import GaloisForLFunctions.RHTower.SoninCoupledBernsteinMismatchRH
import GaloisForLFunctions.RHTower.SoninCoupledNormalizedDeterminantCollar

/-!
# Coupled-Sonin relative determinant RH universality

For a nonnegative sequence, the limit definition of zero exponential rate is equivalent to the
existence of every arbitrarily thin exponential envelope.  Applying this general equivalence to
endpoint Bernstein purity and then transporting across the exact coupled-Sonin determinant-defect
identity upgrades the known one-way source criterion to an equivalence with RH.

The resulting law is aperture-universal: every nondegenerate coupled-Sonin aperture gives a
different concrete normalized relative determinant, but its logarithmic-derivative Bernstein
purity has a unit collar exactly when RH holds.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Zero exponential rate supplies every arbitrarily thin global exponential envelope. -/
theorem unitCollarExponentialEnvelope_of_subexponentialSquareEnergyAtNatInfinity
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

/-- For nonnegative sequences, thin global collars and zero exponential rate are equivalent. -/
theorem subexponentialSquareEnergyAtNatInfinity_iff_unitCollarExponentialEnvelope
    {E : ℕ → ℝ} (hE : ∀ n, 0 ≤ E n) :
    SubexponentialSquareEnergyAtNatInfinity E ↔
      UnitCollarExponentialEnvelope E := by
  exact ⟨unitCollarExponentialEnvelope_of_subexponentialSquareEnergyAtNatInfinity,
    subexponentialSquareEnergyAtNatInfinity_of_unitCollarExponentialEnvelope hE⟩

/-- **Coupled-Sonin relative determinant RH universality law.**  For every nondegenerate aperture,
RH is equivalent to arbitrarily thin exponential Bernstein-purity collars for the logarithmic
derivative coefficients of its concrete normalized relative spectral determinant. -/
theorem riemannHypothesis_iff_soninCoupledRelativeDeterminant_unitCollar
    (a : SoninCoupledNondegenerateAperture) :
    RiemannHypothesis ↔
      UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) := by
  exact riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential.trans
    ((subexponentialSquareEnergyAtNatInfinity_iff_unitCollarExponentialEnvelope
      (fun n => bernsteinCoefficientPurity_nonneg _ n)).trans
        (primeArchEndpoint_unitCollarEnvelope_iff_relativeDeterminantPurity a))

/-- **Coupled-Sonin mismatch classification.**  At every nondegenerate aperture, arbitrarily
thin exponential bounds for the concrete endpoint/source mismatch are exactly RH. -/
theorem riemannHypothesis_iff_soninCoupledEndpointBernsteinMismatch_unitCollar
    (a : SoninCoupledNondegenerateAperture) :
    RiemannHypothesis ↔
      UnitCollarExponentialEnvelope (soninCoupledEndpointBernsteinMismatch a) := by
  have hseq : soninCoupledEndpointBernsteinMismatch a = fun n =>
      bernsteinCoefficientPurity
        (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n := by
    funext n
    exact soninCoupledEndpointBernsteinMismatch_eq_relativeDeterminantPurity a n
  rw [hseq]
  exact riemannHypothesis_iff_soninCoupledRelativeDeterminant_unitCollar a

end

end RHTower
