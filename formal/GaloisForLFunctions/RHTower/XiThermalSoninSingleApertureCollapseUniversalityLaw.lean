import GaloisForLFunctions.RHTower.PrimeArchThermalSoninDeterminantEndpointUniversalityLaw
import GaloisForLFunctions.RHTower.SoninCoupledRelativeDeterminantRHUniversalityLaw

/-!
# Xi thermal--Sonin single-aperture collapse

The enlarged endpoint certificate contains every existing thermal chart and the determinant collar
of every nondegenerate coupled-Sonin aperture.  Its source equivalence and the aperturewise RH
equivalence together show that this entire certificate is already detected by any one aperture.
-/

namespace RHTower

noncomputable section

/-- The simultaneous thermal and all-aperture Sonin endpoint certificate is exactly RH. -/
theorem riemannHypothesis_iff_XiPrimeArchThermalSoninEndpointUniversalCertificate
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔ XiPrimeArchThermalSoninEndpointUniversalCertificate := by
  exact (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one hL hN).trans
    (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalSoninEndpointCertificate
      hL hN)

/-- **Thermal--Sonin single-aperture collapse universality law.**  Under any admissible rectangular
source window, the complete thirty-one-chart thermal certificate together with collars at every
nondegenerate aperture is equivalent to the collar of each single nondegenerate Sonin aperture. -/
theorem XiPrimeArchThermalSoninEndpointUniversalCertificate_iff_singleAperture
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (a : SoninCoupledNondegenerateAperture) :
    XiPrimeArchThermalSoninEndpointUniversalCertificate ↔
      UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) := by
  exact (riemannHypothesis_iff_XiPrimeArchThermalSoninEndpointUniversalCertificate
    hL hN).symm.trans
      (riemannHypothesis_iff_soninCoupledRelativeDeterminant_unitCollar a)

end

end RHTower
