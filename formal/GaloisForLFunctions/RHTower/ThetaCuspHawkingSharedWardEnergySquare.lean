import GaloisForLFunctions.RHTower.ReflectedBiHeatFZZDeningerInformationWardTransmutation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPeierlsDarbouxOrbitOpticalTransgression

/-!
# HB optical power as the shared RBH/FZZ-P/PW-B/Deninger Ward-energy square

Canonical HB Peierls--Darboux optical power is exactly the square of the shared signed Deninger
Ward charge times a strictly positive, source-faithful HB multiplier.  Exact positive-ratio
identities then identify the same power with the squares of the FZZ information force, every-grade
Parikh--Wilczek partner imbalance, and actual RBH multiplicity-leading norm imbalance.

Thus RBH, FZZ-P, PW-B, and Deninger retain linear orientation, whereas passive HB optics sees the
same coordinate only quadratically.  This is an exact energy transmutation and an orientation
no-go: positivity preserves the RH zero locus but cannot itself force the energy to vanish.

`[NEW] [WARD ENERGY] [EXACT MAGNITUDE] [POSITIVE MULTIPLIER] [LEAN-PROVED]`
-/

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Strictly positive HB conversion factor from squared Ward displacement to canonical optical
power.  It retains grade weight, actual Xi height, and full-Einstein radiation norm. -/
def hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  4 * (8 * (n : ℝ) + 5) * (q.1 : ℂ).im ^ 2 *
    ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q), 0)‖ ^ 2

/-- Every factor in the canonical HB Ward-energy conversion is strictly positive. -/
theorem hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier n q := by
  have him : 0 < (q.1 : ℂ).im ^ 2 :=
    sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
  have hradiates :
      d4BMGaugeFixedSecondHarmonicRadiationMap q
        (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q), 0) ≠ 0 :=
    d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_ne_zero (by norm_num) q 0
  have hnorm : 0 < ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q), 0)‖ :=
    norm_pos_iff.mpr hradiates
  rw [hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier]
  positivity

/-- Exact HB/Deninger identity: canonical optical power is positive multiplier times squared
reflect-gauge Ward charge. -/
theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_wardEnergyMultiplier_mul_charge_sq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q =
      hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier n q *
        (fzzCigarParityDeningerReflectGaugeWardCharge q).re ^ 2 := by
  rw [hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower,
    hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower,
    hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux,
    d4BMXiTransportedOrthogonalHelicityMixingFlux,
    normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_tilt,
    hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp only [deningerDivisorThetaEigen, ofReal_re]
  norm_num
  ring

/-- Exact HB/FZZ-P identity through a strictly positive squared information ratio. -/
theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_informationRatio_mul_force_sq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q =
      (hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier n q /
          fzzCigarParityDeningerInformationWardMultiplier
              (deningerDivisorThetaEigen q).re ^ 2) *
        fzzCigarParityReflectedFermiInformationForce
            (deningerDivisorThetaEigen q).re ^ 2 := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hCpos := fzzCigarParityDeningerInformationWardMultiplier_pos h0 h1
  have hC : fzzCigarParityDeningerInformationWardMultiplier
      (deningerDivisorThetaEigen q).re ≠ 0 := ne_of_gt hCpos
  rw [hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_wardEnergyMultiplier_mul_charge_sq,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq,
    fzzCigarParityReflectedFermiInformationForce_eq_centered_mul_wardMultiplier]
  simp only [ofReal_re]
  field_simp [hC]
  ring

/-- Exact HB/PW-B identity at every recoil grade through a strictly positive squared ratio. -/
theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_pwRatio_mul_imbalance_sq
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q =
      (hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier n q /
          schwarzschildParikhWilczekDeningerWardMultiplier k ^ 2) *
        schwarzschildParikhWilczekBorelPartnerRealImbalance
            (deningerDivisorThetaEigen q) k ^ 2 := by
  have hPpos := schwarzschildParikhWilczekDeningerWardMultiplier_pos k
  have hP : schwarzschildParikhWilczekDeningerWardMultiplier k ≠ 0 := ne_of_gt hPpos
  rw [hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_wardEnergyMultiplier_mul_charge_sq,
    schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_neg_wardMultiplier_mul_charge]
  field_simp [hP]

/-- Exact HB/RBH identity on actual Xi support through a strictly positive squared ratio. -/
theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_rbhRatio_mul_imbalance_sq
    (n : ℕ) (rho : XiDivisorSupport) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n
        (reflectedBiHeatFirstDivisorCopy rho) =
      (4 * hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier n
          (reflectedBiHeatFirstDivisorCopy rho) /
        reflectedBiHeatMultiplicityInformationWardMultiplier rho ^ 2) *
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho ^ 2 := by
  have hRpos := reflectedBiHeatMultiplicityInformationWardMultiplier_pos rho
  have hR : reflectedBiHeatMultiplicityInformationWardMultiplier rho ≠ 0 := ne_of_gt hRpos
  rw [hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_wardEnergyMultiplier_mul_charge_sq,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq,
    reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_centered_mul_wardMultiplier]
  simp only [deningerDivisorThetaEigen_reflectedBiHeatFirstDivisorCopy, ofReal_re]
  field_simp [hR]
  ring

/-- HB optical darkness and Deninger Ward cancellation are the same pointwise condition. -/
theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_sharedWardCharge
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 ↔
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0 := by
  rw [hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_line,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq_zero_iff]
  rfl

/-- HB optical darkness and FZZ-P information equilibrium are pointwise identical. -/
theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_informationForce
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 ↔
      fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re = 0 := by
  rw [hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_sharedWardCharge,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq_zero_iff]
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  exact (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).symm

/-- HB optical darkness and PW-B partner balance are pointwise identical at every grade. -/
theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_pwBorelPartnerBalance
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k = 0 := by
  rw [hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_informationForce]
  exact (schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_zero_iff_informationForce
    q k).symm

/-- HB optical darkness and actual RBH multiplicity-leading balance are pointwise identical. -/
theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rbhBalance
    (n : ℕ) (rho : XiDivisorSupport) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n
        (reflectedBiHeatFirstDivisorCopy rho) = 0 ↔
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 := by
  rw [hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_informationForce]
  exact (reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero_iff_informationForce
    rho).symm

end

end RHTower
