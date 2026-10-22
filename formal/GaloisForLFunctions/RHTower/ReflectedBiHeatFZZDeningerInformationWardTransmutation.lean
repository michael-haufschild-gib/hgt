import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityLeadingJetBalance
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekFZZDeningerWardTransmutation

/-!
# RBH/FZZ-P/PW-B/Deninger multiplicity-information Ward transmutation

The actual multiplicity-leading reflected bi-heat norm imbalance is the centered horizontal
displacement times a strictly positive source-faithful multiplier.  Consequently it is exactly a
positive renormalization of the nonlinear FZZ information force and the Parikh--Wilczek Borel
partner imbalance, and a negative multiple of the Deninger reflect-gauge Ward charge.

This identifies magnitude, sign, and zero locus across four receiver languages.  It does not force
the common charge to vanish; the missing step remains an independent source or physical Ward law.

`[NEW] [TRANSMUTATION] [EXACT MAGNITUDE] [ORIENTATION] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Aperture-two imbalance between actual multiplicity-leading reflected bi-heat channel norms. -/
def reflectedBiHeatMultiplicityLeadingJetNormImbalance (rho : XiDivisorSupport) : ℝ :=
  ‖iteratedDeriv (xiSupportMultiplicity rho)
      (reflectedBiHeatLeftResponse 2) (rho : ℂ)‖ -
    ‖iteratedDeriv (xiSupportMultiplicity rho)
      (reflectedBiHeatRightResponse 2) (rho : ℂ)‖

/-- Exact coefficient-and-scale formula for the RBH multiplicity-leading norm imbalance. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq (rho : XiDivisorSupport) :
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho =
      ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
        ((2 : ℝ) ^ reflectedBiHeatLeftScaleOrder (rho : ℂ) -
          (2 : ℝ) ^ reflectedBiHeatRightScaleOrder (rho : ℂ)) := by
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance,
    norm_reflectedBiHeatLeftResponse_leadingJet_two,
    norm_reflectedBiHeatRightResponse_leadingJet_two]
  ring

/-- Left-of-center actual divisors have strictly negative RBH norm imbalance. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_neg_of_lt_half
    (rho : XiDivisorSupport) (hlt : (rho : ℂ).re < 1 / 2) :
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho < 0 := by
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq]
  have hcoef : 0 < ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ :=
    norm_pos_iff.mpr (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)
  have horders : reflectedBiHeatLeftScaleOrder (rho : ℂ) <
      reflectedBiHeatRightScaleOrder (rho : ℂ) := by
    rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
    linarith
  have hpowers : (2 : ℝ) ^ reflectedBiHeatLeftScaleOrder (rho : ℂ) <
      (2 : ℝ) ^ reflectedBiHeatRightScaleOrder (rho : ℂ) :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)) horders
  nlinarith

/-- Right-of-center actual divisors have strictly positive RBH norm imbalance. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_pos_of_half_lt
    (rho : XiDivisorSupport) (hgt : 1 / 2 < (rho : ℂ).re) :
    0 < reflectedBiHeatMultiplicityLeadingJetNormImbalance rho := by
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq]
  have hcoef : 0 < ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ :=
    norm_pos_iff.mpr (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)
  have horders : reflectedBiHeatRightScaleOrder (rho : ℂ) <
      reflectedBiHeatLeftScaleOrder (rho : ℂ) := by
    rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
    linarith
  have hpowers : (2 : ℝ) ^ reflectedBiHeatRightScaleOrder (rho : ℂ) <
      (2 : ℝ) ^ reflectedBiHeatLeftScaleOrder (rho : ℂ) :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)) horders
  nlinarith

/-- Source-faithful conversion factor from horizontal displacement to actual RBH norm imbalance. -/
def reflectedBiHeatMultiplicityInformationWardMultiplier (rho : XiDivisorSupport) : ℝ :=
  if (rho : ℂ).re = 1 / 2 then
    ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖
  else
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho / ((rho : ℂ).re - 1 / 2)

/-- Exact centered factorization of the actual RBH multiplicity-leading imbalance. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_centered_mul_wardMultiplier
    (rho : XiDivisorSupport) :
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho =
      ((rho : ℂ).re - 1 / 2) *
        reflectedBiHeatMultiplicityInformationWardMultiplier rho := by
  by_cases hcenter : (rho : ℂ).re = 1 / 2
  · rw [reflectedBiHeatMultiplicityInformationWardMultiplier, if_pos hcenter, hcenter]
    norm_num
    rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance, sub_eq_zero]
    exact (reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff rho).mpr hcenter
  · rw [reflectedBiHeatMultiplicityInformationWardMultiplier, if_neg hcenter]
    have hdenom : (rho : ℂ).re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hcenter
    have hdenom' : (rho : ℂ).re * 2 - 1 ≠ 0 := by
      intro hz
      apply hcenter
      linarith
    field_simp [hdenom, hdenom']

/-- RBH conversion is strictly positive at every actual Xi divisor, including the center. -/
theorem reflectedBiHeatMultiplicityInformationWardMultiplier_pos (rho : XiDivisorSupport) :
    0 < reflectedBiHeatMultiplicityInformationWardMultiplier rho := by
  by_cases hcenter : (rho : ℂ).re = 1 / 2
  · rw [reflectedBiHeatMultiplicityInformationWardMultiplier, if_pos hcenter]
    exact norm_pos_iff.mpr (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)
  · rw [reflectedBiHeatMultiplicityInformationWardMultiplier, if_neg hcenter]
    rcases lt_or_gt_of_ne hcenter with hlt | hgt
    · exact div_pos_of_neg_of_neg
        (reflectedBiHeatMultiplicityLeadingJetNormImbalance_neg_of_lt_half rho hlt)
        (by linarith)
    · exact div_pos
        (reflectedBiHeatMultiplicityLeadingJetNormImbalance_pos_of_half_lt rho hgt)
        (by linarith)

/-- Canonical first divisor-flow copy of an actual Xi divisor. -/
def reflectedBiHeatFirstDivisorCopy (rho : XiDivisorSupport) : XiZeroCopy :=
  ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩

@[simp] theorem deningerDivisorThetaEigen_reflectedBiHeatFirstDivisorCopy
    (rho : XiDivisorSupport) :
    deningerDivisorThetaEigen (reflectedBiHeatFirstDivisorCopy rho) = (rho : ℂ) := rfl

/-- Exact RBH/Deninger transmutation on an actual divisor's canonical first copy. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_neg_half_wardMultiplier_mul_charge
    (rho : XiDivisorSupport) :
    ((reflectedBiHeatMultiplicityLeadingJetNormImbalance rho : ℝ) : ℂ) =
      -((reflectedBiHeatMultiplicityInformationWardMultiplier rho / 2 : ℝ) : ℂ) *
        fzzCigarParityDeningerReflectGaugeWardCharge
          (reflectedBiHeatFirstDivisorCopy rho) := by
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_centered_mul_wardMultiplier,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp only [deningerDivisorThetaEigen_reflectedBiHeatFirstDivisorCopy]
  push_cast
  ring

/-- Exact RBH/FZZ-P transmutation through a strictly positive conversion ratio. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_informationRatio_mul_force
    (rho : XiDivisorSupport) :
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho =
      (reflectedBiHeatMultiplicityInformationWardMultiplier rho /
          (2 * fzzCigarParityDeningerInformationWardMultiplier (rho : ℂ).re)) *
        fzzCigarParityReflectedFermiInformationForce (rho : ℂ).re := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
  have hCpos := fzzCigarParityDeningerInformationWardMultiplier_pos h0 h1
  have hC : fzzCigarParityDeningerInformationWardMultiplier (rho : ℂ).re ≠ 0 :=
    ne_of_gt hCpos
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_centered_mul_wardMultiplier,
    fzzCigarParityReflectedFermiInformationForce_eq_centered_mul_wardMultiplier]
  field_simp [hC]

/-- RBH and FZZ-P have identical strict orientation away from the critical line. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_mul_informationForce_pos
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    0 < reflectedBiHeatMultiplicityLeadingJetNormImbalance rho *
      fzzCigarParityReflectedFermiInformationForce (rho : ℂ).re := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
  have hR := reflectedBiHeatMultiplicityInformationWardMultiplier_pos rho
  have hC := fzzCigarParityDeningerInformationWardMultiplier_pos h0 h1
  have hF : fzzCigarParityReflectedFermiInformationForce (rho : ℂ).re ≠ 0 := by
    intro hzero
    exact hoff ((fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).mp hzero)
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_informationRatio_mul_force]
  have hratio : 0 < reflectedBiHeatMultiplicityInformationWardMultiplier rho /
      (2 * fzzCigarParityDeningerInformationWardMultiplier (rho : ℂ).re) := by positivity
  nlinarith [sq_pos_of_ne_zero hF]

/-- Pointwise RBH balance is exactly FZZ-P information equilibrium. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero_iff_informationForce
    (rho : XiDivisorSupport) :
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 ↔
      fzzCigarParityReflectedFermiInformationForce (rho : ℂ).re = 0 := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance, sub_eq_zero,
    reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff,
    fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1]

/-- Exact RBH/PW-B transmutation through a strictly positive conversion ratio. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_pwRatio_mul_imbalance
    (rho : XiDivisorSupport) (k : ℕ) :
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho =
      (reflectedBiHeatMultiplicityInformationWardMultiplier rho /
          (2 * schwarzschildParikhWilczekDeningerWardMultiplier k)) *
        schwarzschildParikhWilczekBorelPartnerRealImbalance (rho : ℂ) k := by
  have hPpos := schwarzschildParikhWilczekDeningerWardMultiplier_pos k
  have hP : schwarzschildParikhWilczekDeningerWardMultiplier k ≠ 0 := ne_of_gt hPpos
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_centered_mul_wardMultiplier]
  change ((rho : ℂ).re - 1 / 2) *
      reflectedBiHeatMultiplicityInformationWardMultiplier rho =
    (reflectedBiHeatMultiplicityInformationWardMultiplier rho /
        (2 * schwarzschildParikhWilczekDeningerWardMultiplier k)) *
      schwarzschildParikhWilczekBorelPartnerRealImbalance
        (deningerDivisorThetaEigen (reflectedBiHeatFirstDivisorCopy rho)) k
  rw [schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_neg_wardMultiplier_mul_charge,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp only [deningerDivisorThetaEigen_reflectedBiHeatFirstDivisorCopy, ofReal_re]
  field_simp [hP]
  ring

/-- Pointwise RBH balance is exactly PW-B partner balance at every recoil grade. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero_iff_pwBorelPartnerBalance
    (rho : XiDivisorSupport) (k : ℕ) :
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance (rho : ℂ) k = 0 := by
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero_iff_informationForce]
  exact (schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_zero_iff_informationForce
    (reflectedBiHeatFirstDivisorCopy rho) k).symm

/-- Pointwise RBH balance is exactly Deninger reflect-gauge equivariance. -/
theorem reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero_iff_deningerReflectGauge_comm
    (rho : XiDivisorSupport) :
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 ↔
      deningerDivisorTheta
          (deningerDivisorReflectGauge (Finsupp.single (reflectedBiHeatFirstDivisorCopy rho) 1)) =
        deningerDivisorReflectGauge
          (deningerDivisorTheta (Finsupp.single (reflectedBiHeatFirstDivisorCopy rho) 1)) := by
  rw [reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero_iff_informationForce]
  exact fzzCigarParityInformationForce_eq_zero_iff_deningerReflectGauge_comm
    (reflectedBiHeatFirstDivisorCopy rho)

/-- Universal vanishing of the actual RBH norm imbalance is exactly RH. -/
theorem riemannHypothesis_iff_reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 := by
  rw [riemannHypothesis_iff_reflectedBiHeatMultiplicityLeadingJetNorms_two_eq]
  simp only [reflectedBiHeatMultiplicityLeadingJetNormImbalance, sub_eq_zero]

end

end RHTower
