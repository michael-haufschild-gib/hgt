import GaloisForLFunctions.RHTower.FZZCigarParityDeningerInformationWardTransmutation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint

/-!
# PW-B/FZZ-P/Deninger recoil--information--Ward transmutation

First-winding Parikh--Wilczek partner-growth imbalance, nonlinear FZZ information force, and the
Deninger reflect-gauge commutator are the same oriented divisor charge up to strictly positive
conversion factors.
-/

open Complex

namespace RHTower

noncomputable section

/-- Real first-winding PW Borel growth imbalance against the functional-equation partner. -/
def schwarzschildParikhWilczekBorelPartnerRealImbalance (s : ℂ) (k : ℕ) : ℝ :=
  (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio s k).re -
    (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio (1 - s) k).re

/-- Positive conversion factor from Deninger displacement charge to PW Borel imbalance. -/
def schwarzschildParikhWilczekDeningerWardMultiplier (k : ℕ) : ℝ :=
  (2 * (2 * (k : ℝ) + 1)) / (k + 1 : ℝ) ^ (2 : ℕ)

theorem schwarzschildParikhWilczekDeningerWardMultiplier_pos (k : ℕ) :
    0 < schwarzschildParikhWilczekDeningerWardMultiplier k := by
  rw [schwarzschildParikhWilczekDeningerWardMultiplier]
  positivity

/-- Exact PW-B/Deninger transmutation on every actual divisor copy. -/
theorem schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_neg_wardMultiplier_mul_charge
    (q : XiZeroCopy) (k : ℕ) :
    schwarzschildParikhWilczekBorelPartnerRealImbalance
        (deningerDivisorThetaEigen q) k =
      -schwarzschildParikhWilczekDeningerWardMultiplier k *
        (fzzCigarParityDeningerReflectGaugeWardCharge q).re := by
  rw [schwarzschildParikhWilczekBorelPartnerRealImbalance,
    schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_re_sub_partner,
    schwarzschildParikhWilczekDeningerWardMultiplier,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp only [ofReal_re]
  ring

/-- Exact PW-B/FZZ-P transmutation: recoil imbalance is a positive multiple of nonlinear source
force, with the positive HC38 information multiplier as denominator. -/
theorem schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_informationRatio_mul_force
    (q : XiZeroCopy) (k : ℕ) :
    schwarzschildParikhWilczekBorelPartnerRealImbalance
        (deningerDivisorThetaEigen q) k =
      (schwarzschildParikhWilczekDeningerWardMultiplier k /
          fzzCigarParityDeningerInformationWardMultiplier
            (deningerDivisorThetaEigen q).re) *
        fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hCpos := fzzCigarParityDeningerInformationWardMultiplier_pos h0 h1
  have hC : fzzCigarParityDeningerInformationWardMultiplier
      (deningerDivisorThetaEigen q).re ≠ 0 := ne_of_gt hCpos
  rw [schwarzschildParikhWilczekBorelPartnerRealImbalance,
    schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_re_sub_partner,
    schwarzschildParikhWilczekDeningerWardMultiplier,
    fzzCigarParityReflectedFermiInformationForce_eq_centered_mul_wardMultiplier]
  field_simp [hC]
  ring

/-- PW recoil imbalance and FZZ information force have exactly the same strict orientation away
from the critical line. -/
theorem schwarzschildParikhWilczekBorelPartnerRealImbalance_mul_informationForce_pos
    (q : XiZeroCopy) (k : ℕ)
    (hoff : (deningerDivisorThetaEigen q).re ≠ 1 / 2) :
    0 < schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k *
        fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hP := schwarzschildParikhWilczekDeningerWardMultiplier_pos k
  have hC := fzzCigarParityDeningerInformationWardMultiplier_pos h0 h1
  have hF : fzzCigarParityReflectedFermiInformationForce
      (deningerDivisorThetaEigen q).re ≠ 0 := by
    intro hzero
    exact hoff ((fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).mp hzero)
  rw [schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_informationRatio_mul_force]
  have hratio : 0 < schwarzschildParikhWilczekDeningerWardMultiplier k /
      fzzCigarParityDeningerInformationWardMultiplier
        (deningerDivisorThetaEigen q).re := div_pos hP hC
  nlinarith [sq_pos_of_ne_zero hF]

/-- Pointwise balance/equilibrium identity between PW-B and FZZ-P. -/
theorem schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_zero_iff_informationForce
    (q : XiZeroCopy) (k : ℕ) :
    schwarzschildParikhWilczekBorelPartnerRealImbalance
        (deningerDivisorThetaEigen q) k = 0 ↔
      fzzCigarParityReflectedFermiInformationForce
        (deningerDivisorThetaEigen q).re = 0 := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  rw [schwarzschildParikhWilczekBorelPartnerRealImbalance, sub_eq_zero,
    schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_partner_re_eq_iff]
  change (q.1 : ℂ).re = 1 / 2 ↔
    fzzCigarParityReflectedFermiInformationForce (q.1 : ℂ).re = 0
  exact (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).symm

/-- Pointwise balance/equivariance identity between PW-B and the Deninger reflect gauge. -/
theorem schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_zero_iff_deningerReflectGauge_comm
    (q : XiZeroCopy) (k : ℕ) :
    schwarzschildParikhWilczekBorelPartnerRealImbalance
        (deningerDivisorThetaEigen q) k = 0 ↔
      deningerDivisorTheta (deningerDivisorReflectGauge (Finsupp.single q 1)) =
        deningerDivisorReflectGauge (deningerDivisorTheta (Finsupp.single q 1)) := by
  rw [schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_zero_iff_informationForce,
    fzzCigarParityInformationForce_eq_zero_iff_deningerReflectGauge_comm]

/-- Universal PW Borel partner balance at one fixed recoil grade over the actual Xi divisor. -/
def SchwarzschildParikhWilczekBorelPartnerBalancedAtGrade (k : ℕ) : Prop :=
  ∀ q : XiZeroCopy,
    schwarzschildParikhWilczekBorelPartnerRealImbalance
      (deningerDivisorThetaEigen q) k = 0

/-- One recoil grade already carries exactly the shared RH Ward endpoint. -/
theorem schwarzschildParikhWilczekBorelPartnerBalancedAtGrade_iff_riemannHypothesis
    (k : ℕ) :
    SchwarzschildParikhWilczekBorelPartnerBalancedAtGrade k ↔ RiemannHypothesis := by
  constructor
  · intro hbalance
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    have himbalance :
        schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k = 0 := hbalance q
    rw [schwarzschildParikhWilczekBorelPartnerRealImbalance, sub_eq_zero,
      schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_partner_re_eq_iff]
      at himbalance
    exact himbalance
  · intro hRH q
    have hforce :=
      (fzzCigarParityDeningerInformationWardEquilibrium_iff_riemannHypothesis.mpr hRH) q
    exact (schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_zero_iff_informationForce
      q k).mpr hforce

theorem riemannHypothesis_iff_schwarzschildParikhWilczekBorelPartnerBalancedAtGrade
    (k : ℕ) :
    RiemannHypothesis ↔ SchwarzschildParikhWilczekBorelPartnerBalancedAtGrade k :=
  (schwarzschildParikhWilczekBorelPartnerBalancedAtGrade_iff_riemannHypothesis k).symm

end

end RHTower
