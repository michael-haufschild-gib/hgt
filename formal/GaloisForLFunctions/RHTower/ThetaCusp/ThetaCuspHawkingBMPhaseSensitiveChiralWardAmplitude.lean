import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSharedWardEnergySquare
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer

/-!
# Phase-sensitive BM chiral amplitude as the shared signed Ward coordinate

The actual nonlinear BM mixed-horizon source projection factors linearly through the Deninger
reflect-gauge Ward charge.  Its remaining factor is a nonzero complex number for every nonzero
Einstein seed: imaginary Xi height, retarded ingoing Green transfer, and nonlinear carrier.

Dividing by this known factor reconstructs the signed charge itself.  This is the phase-sensitive
square root of the passive HB Ward-energy law: it retains left/right orientation that squared
optical power necessarily loses.  Exact complex-ratio identities identify the same amplitude with
the FZZ information force, every-grade Parikh--Wilczek imbalance, and actual RBH
multiplicity-leading imbalance.

The construction is a faithful receiver, not a producer.  Universal cancellation of this actual
source projection is proved equivalent to RH, so a source-native conservation law forcing that
cancellation remains the precise open burden.

`[NEW] [PHASE-SENSITIVE] [EXACT AMPLITUDE] [ORIENTATION] [LEAN-PROVED]`
-/

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Exact signed factorization of the BM orthogonal-helicity coefficient.  Unlike its norm square,
this complex amplitude retains the orientation of the critical displacement. -/
theorem d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_im_mul_deningerCharge
    (q : XiZeroCopy) :
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q =
      Complex.I * (((q.1 : ℂ).im : ℝ) : ℂ) *
        fzzCigarParityDeningerReflectGaugeWardCharge q := by
  rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq,
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp only [deningerDivisorThetaEigen, xiSpectralPoint]
  apply Complex.ext
  · simp [pow_two, Complex.mul_re, Complex.mul_im]
  · simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring

/-- Complex conversion factor from Deninger charge to the actual BM nonlinear horizon source
projection. -/
def hbXiPhaseSensitiveChiralWardMultiplier (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  Complex.I * (((q.1 : ℂ).im : ℝ) : ℂ) *
    (d4BMGaugeFixedSecondHarmonicGreen q *
      d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
        (xiSpectralPoint q))

/-- Nonzero Einstein seed makes every factor in the phase-sensitive HB conversion faithful. -/
theorem hbXiPhaseSensitiveChiralWardMultiplier_ne_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    hbXiPhaseSensitiveChiralWardMultiplier amplitude q ≠ 0 := by
  rw [hbXiPhaseSensitiveChiralWardMultiplier]
  exact mul_ne_zero
    (mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr (xi_divisor_support_im_ne_zero q.1)))
    (mul_ne_zero (d4BMGaugeFixedSecondHarmonicGreen_ne_zero q)
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q))

/-- Actual nonlinear BM mixed-horizon amplitude is exactly a complex multiplier times the common
signed Ward charge.  The arbitrary orthogonal source coordinate remains absent. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q =
      hbXiPhaseSensitiveChiralWardMultiplier amplitude q *
        fzzCigarParityDeningerReflectGaugeWardCharge q := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_im_mul_deningerCharge,
    hbXiPhaseSensitiveChiralWardMultiplier]
  ring

/-- Calibration removes only known physical propagation and source factors. -/
def hbXiCalibratedPhaseSensitiveChiralWardAmplitude
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q /
    hbXiPhaseSensitiveChiralWardMultiplier amplitude q

/-- A nonzero nonlinear seed makes calibrated HB chiral amplitude equal the signed Deninger charge,
not merely its squared magnitude. -/
theorem hbXiCalibratedPhaseSensitiveChiralWardAmplitude_eq_deningerCharge
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiCalibratedPhaseSensitiveChiralWardAmplitude amplitude orthogonalMixing q =
      fzzCigarParityDeningerReflectGaugeWardCharge q := by
  rw [hbXiCalibratedPhaseSensitiveChiralWardAmplitude,
    d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge]
  exact mul_div_cancel_left₀ _ (hbXiPhaseSensitiveChiralWardMultiplier_ne_zero ha q)

/-- Calibrated phase-sensitive amplitude reconstructs signed horizontal displacement exactly. -/
theorem hbXiCalibratedPhaseSensitiveChiralWardAmplitude_re_eq
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    (hbXiCalibratedPhaseSensitiveChiralWardAmplitude
      amplitude orthogonalMixing q).re = 1 - 2 * (q.1 : ℂ).re := by
  rw [hbXiCalibratedPhaseSensitiveChiralWardAmplitude_eq_deningerCharge ha,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  rfl

/-- Calibrated chiral amplitude is a real Ward coordinate inside the complex response channel. -/
theorem hbXiCalibratedPhaseSensitiveChiralWardAmplitude_im_eq_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    (hbXiCalibratedPhaseSensitiveChiralWardAmplitude
      amplitude orthogonalMixing q).im = 0 := by
  rw [hbXiCalibratedPhaseSensitiveChiralWardAmplitude_eq_deningerCharge ha,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp

/-- Left-of-center Xi divisors give positive calibrated HB chiral orientation. -/
theorem hbXiCalibratedPhaseSensitiveChiralWardAmplitude_re_pos_of_lt_half
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hlt : (q.1 : ℂ).re < 1 / 2) :
    0 < (hbXiCalibratedPhaseSensitiveChiralWardAmplitude
      amplitude orthogonalMixing q).re := by
  rw [hbXiCalibratedPhaseSensitiveChiralWardAmplitude_re_eq ha]
  linarith

/-- Right-of-center Xi divisors give negative calibrated HB chiral orientation. -/
theorem hbXiCalibratedPhaseSensitiveChiralWardAmplitude_re_neg_of_half_lt
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hgt : 1 / 2 < (q.1 : ℂ).re) :
    (hbXiCalibratedPhaseSensitiveChiralWardAmplitude
      amplitude orthogonalMixing q).re < 0 := by
  rw [hbXiCalibratedPhaseSensitiveChiralWardAmplitude_re_eq ha]
  linarith

/-- Exact HB/FZZ-P complex-amplitude transmutation. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq_fzzInformationRatio_mul_force
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q =
      -(hbXiPhaseSensitiveChiralWardMultiplier amplitude q /
          (fzzCigarParityDeningerInformationWardMultiplier
            (deningerDivisorThetaEigen q).re : ℂ)) *
        ((fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re : ℝ) : ℂ) := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hCpos := fzzCigarParityDeningerInformationWardMultiplier_pos h0 h1
  have hC : fzzCigarParityDeningerInformationWardMultiplier
      (deningerDivisorThetaEigen q).re ≠ 0 := ne_of_gt hCpos
  rw [d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge,
    fzzCigarParityInformationForce_eq_neg_wardMultiplier_mul_deningerCharge]
  field_simp [hC]

/-- Exact HB/PW-B complex-amplitude transmutation at every recoil grade. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq_pwRatio_mul_imbalance
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) (k : ℕ) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q =
      -(hbXiPhaseSensitiveChiralWardMultiplier amplitude q /
          (schwarzschildParikhWilczekDeningerWardMultiplier k : ℂ)) *
        ((schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k : ℝ) : ℂ) := by
  have hPpos := schwarzschildParikhWilczekDeningerWardMultiplier_pos k
  have hP : schwarzschildParikhWilczekDeningerWardMultiplier k ≠ 0 := ne_of_gt hPpos
  rw [d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge,
    schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_neg_wardMultiplier_mul_charge,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp only [ofReal_re]
  push_cast
  field_simp [hP]

/-- Exact HB/RBH complex-amplitude transmutation on an actual divisor's canonical first copy. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq_rbhRatio_mul_imbalance
    (amplitude orthogonalMixing : ℂ) (rho : XiDivisorSupport) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing
        (reflectedBiHeatFirstDivisorCopy rho) =
      -(2 * hbXiPhaseSensitiveChiralWardMultiplier amplitude
          (reflectedBiHeatFirstDivisorCopy rho) /
          (reflectedBiHeatMultiplicityInformationWardMultiplier rho : ℂ)) *
        ((reflectedBiHeatMultiplicityLeadingJetNormImbalance rho : ℝ) : ℂ) := by
  have hRpos := reflectedBiHeatMultiplicityInformationWardMultiplier_pos rho
  have hR : reflectedBiHeatMultiplicityInformationWardMultiplier rho ≠ 0 := ne_of_gt hRpos
  rw [d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge,
    reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_neg_half_wardMultiplier_mul_charge]
  field_simp [hR]
  push_cast
  ring

/-- For nonzero seed, actual phase-sensitive source darkness is exactly Ward cancellation. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_deningerCharge
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q = 0 ↔
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0 := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge,
    mul_eq_zero]
  simp [hbXiPhaseSensitiveChiralWardMultiplier_ne_zero ha q]

/-- Pointwise phase-sensitive HB darkness is exactly critical-line placement. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q = 0 ↔
      (deningerDivisorThetaEigen q).re = 1 / 2 := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_deningerCharge ha,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq_zero_iff]

/-- Pointwise phase-sensitive HB darkness is exactly FZZ-P information equilibrium. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_informationForce
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q = 0 ↔
      fzzCigarParityReflectedFermiInformationForce
        (deningerDivisorThetaEigen q).re = 0 := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half ha]
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  exact (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).symm

/-- Universal cancellation of one fixed nonzero nonlinear HB seed. -/
def HBXiPhaseSensitiveChiralWardAmplitudeCancellation : Prop :=
  ∀ q : XiZeroCopy,
    d4BMMixedHorizonOpticalSourceProjection 1 0 q = 0

/-- Phase-sensitive HB cancellation is RH-strength.  This sharpens the residual producer burden:
deriving the left side from source dynamics, without assuming it, would prove RH. -/
theorem hbXiPhaseSensitiveChiralWardAmplitudeCancellation_iff_riemannHypothesis :
    HBXiPhaseSensitiveChiralWardAmplitudeCancellation ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    exact (d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
      (by norm_num) 0 q).mp (h q)
  · intro hRH q
    apply (d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
      (by norm_num) 0 q).mpr
    exact (deningerDivisorReflectGauge_comm_iff_re_eq_half q).mp
      (deningerDivisorReflectGauge_comm_of_riemannHypothesis hRH q 1)

theorem riemannHypothesis_iff_hbXiPhaseSensitiveChiralWardAmplitudeCancellation :
    RiemannHypothesis ↔ HBXiPhaseSensitiveChiralWardAmplitudeCancellation :=
  hbXiPhaseSensitiveChiralWardAmplitudeCancellation_iff_riemannHypothesis.symm

end

end RHTower
