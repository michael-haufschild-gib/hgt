import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaXiMassPolarizedGreenWeld
import GaloisForLFunctions.RHTower.XiMassHalfDensityAdjacentPrimeConnection

/-!
# Prime-connection / theta-Green anomaly compensation

The half-density adjacent-prime connection and the polarized theta Green packet are not two
independent RH-strength currents.  Their phase-linear sum cancels exactly to the archimedean face
minus the uniformly bounded higher-prime-power remainder.  Thus both open cores represent one
common anomaly modulo the vertical bounded ideal.

This is an unconditional cross-route Ward identity.  It retains the ordered prime connection and
the unsquared theta metric current before their cancellation; no norm or positivity argument is
inserted into the exact identity.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Phase-linear sum of the theta polarized Green packet and the ordered prime connection. -/
def xiMassThetaPrimeConnectionCompensatedPacket
    (a c : ℝ) (tau : ℂ) : ℂ :=
  xiMassThetaQuantileMetricSymplecticIntegral a c tau +
    Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
      xiMassPrimeHalfDensityConnectionLayer a tau

/-- **Cross-route anomaly compensation.**  The theta Green current and the half-density prime
connection cancel to the harmless archimedean and repeated-prime background. -/
theorem xiMassThetaPrimeConnectionCompensatedPacket_eq_arch_sub_nonPrime
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    xiMassThetaPrimeConnectionCompensatedPacket a c tau =
      Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        (xiMassBottomArchIntegral a c tau -
          (xiMassPrimeSquareLayer a tau + xiMassHighPrimePowerTail a tau)) := by
  have hgreen :=
    xiMassThetaQuantileMetricSymplecticIntegral_eq_I_mul_resolventIntegral
      (a := a) hhalf tau
  have hweld := xiMassBottomPrimeIntegral_eq_arch_sub_thetaQuantileResolventIntegral
    hhalf hca htau
  have hprime := xiMassBottomPrimeIntegral_eq_valuationOne_add_square_add_high
    hhalf hca htau
  have hconnection := xiMassPrimeHalfDensityConnectionLayer_eq_valuationOne
    hhalf hca htau
  have hsource :
      xiMassThetaQuantileResolventIntegral a c tau +
          xiMassValuationOnePrimeLayer a tau =
        xiMassBottomArchIntegral a c tau -
          (xiMassPrimeSquareLayer a tau + xiMassHighPrimePowerTail a tau) := by
    linear_combination hweld - hprime
  rw [xiMassThetaPrimeConnectionCompensatedPacket, hgreen, hconnection]
  calc
    Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
          xiMassThetaQuantileResolventIntegral a c tau +
        Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
          xiMassValuationOnePrimeLayer a tau =
      (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
        (xiMassThetaQuantileResolventIntegral a c tau +
          xiMassValuationOnePrimeLayer a tau) := by ring
    _ = _ := by rw [hsource]

/-- The compensated cross-route packet is uniformly bounded on every positive complex-time
vertical line, unconditionally. -/
theorem exists_norm_xiMassThetaPrimeConnectionCompensatedPacket_vertical_bound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖xiMassThetaPrimeConnectionCompensatedPacket a c
        ((sigma : ℂ) + u * Complex.I)‖ ≤ C := by
  let Barch : ℝ := xiMassBottomArchUniformBound a sigma
  obtain ⟨Bprime, hBprime⟩ :=
    exists_norm_xiMassNonPrimeRemainder_vertical_bound
      (show 0 < a by linarith) hsigma
  refine ⟨‖Complex.I * pinnedFirstMoment thetaQuantileCoordinate‖ *
      (Barch + Bprime), fun u => ?_⟩
  have htau : 0 < (((sigma : ℂ) + u * Complex.I)).re := by
    simpa using hsigma
  rw [xiMassThetaPrimeConnectionCompensatedPacket_eq_arch_sub_nonPrime
    hhalf hca htau, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (add_le_add
    (by
      simpa only [Barch, xiMassBottomArchIntegral] using
        norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hsigma)
    (hBprime u))

end

end RHTower
