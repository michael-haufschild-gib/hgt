import GaloisForLFunctions.RHTower.ThetaCuspHawkingMovingHorizonPeierlsOrbitSquareLaw
import GaloisForLFunctions.RHTower.ThetaCuspHawkingSharedWardEnergySquare

/-!
# Peierls-orbit four-route negative-square transmutation

The actual reflected plus-plus/minus-minus BM Peierls current is a negative positive-coefficient multiple of
canonical HB optical power and, equivalently, a negative positive-coefficient square of the FZZ-P
information force, every-grade PW-B partner imbalance, and actual RBH multiplicity-leading
imbalance.

`[NEW] [PEIERLS CAUSAL CURRENT] [FZZ-P] [PW-B] [RBH] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Positive coefficient converting canonical HB optical power to the oppositely oriented
reflected Peierls current. -/
def d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  2 * (8 * (n : ℝ) + 5) * (q.1 : ℂ).im ^ (2 : ℕ) /
    hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier n q

theorem d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility n q := by
  unfold d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility
  exact div_pos (mul_pos (mul_pos (by norm_num) (by positivity))
      (sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)))
    (hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier_pos n q)

/-- The polarized causal current is a strictly negative multiple of canonical HB optical power. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_hbOpticalPower
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q =
      -((d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility n q *
        hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q : ℝ) : ℂ) := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_density,
    d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_tilt,
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_wardEnergyMultiplier_mul_charge_sq,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  unfold d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility
  have hW : hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier n q ≠ 0 :=
    ne_of_gt (hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier_pos n q)
  simp only [ofReal_re, deningerDivisorThetaEigen]
  push_cast
  field_simp [hW]

/-- Positive coefficient converting squared FZZ information force to the reflected Peierls orbit. -/
def d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  2 * (8 * (n : ℝ) + 5) * (q.1 : ℂ).im ^ (2 : ℕ) /
    fzzCigarParityDeningerInformationWardMultiplier
      (deningerDivisorThetaEigen q).re ^ (2 : ℕ)

theorem d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility n q := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  unfold d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility
  exact div_pos (mul_pos (mul_pos (by norm_num) (by positivity))
      (sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)))
    (sq_pos_of_pos (fzzCigarParityDeningerInformationWardMultiplier_pos h0 h1))

/-- Exact FZZ-P presentation of the polarized causal-current orbit. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_fzzForce_sq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q =
      -((d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility n q *
        fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_density,
    d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_tilt,
    fzzCigarParityReflectedFermiInformationForce_eq_centered_mul_wardMultiplier]
  unfold d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hC : fzzCigarParityDeningerInformationWardMultiplier
      (deningerDivisorThetaEigen q).re ≠ 0 :=
    ne_of_gt (fzzCigarParityDeningerInformationWardMultiplier_pos h0 h1)
  simp only [deningerDivisorThetaEigen] at hC ⊢
  push_cast
  field_simp [hC]
  ring

/-- Positive coefficient converting squared every-grade PW-B imbalance to the Peierls orbit. -/
def d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility
    (n k : ℕ) (q : XiZeroCopy) : ℝ :=
  2 * (8 * (n : ℝ) + 5) * (q.1 : ℂ).im ^ (2 : ℕ) /
    schwarzschildParikhWilczekDeningerWardMultiplier k ^ (2 : ℕ)

theorem d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility_pos
    (n k : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility n k q := by
  unfold d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility
  exact div_pos (mul_pos (mul_pos (by norm_num) (by positivity))
      (sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)))
    (sq_pos_of_pos (schwarzschildParikhWilczekDeningerWardMultiplier_pos k))

/-- Exact every-grade PW-B presentation of the polarized causal-current orbit. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_pwImbalance_sq
    (n k : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q =
      -((d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility n k q *
        schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_density,
    d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_tilt,
    schwarzschildParikhWilczekBorelPartnerRealImbalance_eq_neg_wardMultiplier_mul_charge,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  unfold d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility
  have hP : schwarzschildParikhWilczekDeningerWardMultiplier k ≠ 0 :=
    ne_of_gt (schwarzschildParikhWilczekDeningerWardMultiplier_pos k)
  simp only [ofReal_re, deningerDivisorThetaEigen]
  push_cast
  field_simp [hP]

/-- Positive coefficient converting squared actual RBH imbalance to the reflected Peierls orbit. -/
def d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility
    (n : ℕ) (rho : XiDivisorSupport) : ℝ :=
  8 * (8 * (n : ℝ) + 5) * (rho : ℂ).im ^ (2 : ℕ) /
    reflectedBiHeatMultiplicityInformationWardMultiplier rho ^ (2 : ℕ)

theorem d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility_pos
    (n : ℕ) (rho : XiDivisorSupport) :
    0 < d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility n rho := by
  unfold d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility
  exact div_pos (mul_pos (mul_pos (by norm_num) (by positivity))
      (sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero rho)))
    (sq_pos_of_pos (reflectedBiHeatMultiplicityInformationWardMultiplier_pos rho))

/-- Exact actual-RBH presentation of the polarized causal-current orbit. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_rbhImbalance_sq
    (n : ℕ) (rho : XiDivisorSupport) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n
        (reflectedBiHeatFirstDivisorCopy rho) =
      -((d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility n rho *
        reflectedBiHeatMultiplicityLeadingJetNormImbalance rho ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_density,
    d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_tilt,
    reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_centered_mul_wardMultiplier]
  unfold d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility
  have hR : reflectedBiHeatMultiplicityInformationWardMultiplier rho ≠ 0 :=
    ne_of_gt (reflectedBiHeatMultiplicityInformationWardMultiplier_pos rho)
  simp only [reflectedBiHeatFirstDivisorCopy]
  push_cast
  field_simp [hR]
  ring

theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_fzzForce
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q = 0 ↔
      fzzCigarParityReflectedFermiInformationForce
        (deningerDivisorThetaEigen q).re = 0 := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_fzzForce_sq]
  have hS : d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility n q ≠ 0 :=
    ne_of_gt (d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility_pos n q)
  simp [hS]

theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_pwImbalance
    (n k : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q = 0 ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance
        (deningerDivisorThetaEigen q) k = 0 := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_pwImbalance_sq
    n k q]
  have hS : d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility n k q ≠ 0 :=
    ne_of_gt (d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility_pos n k q)
  simp [hS]

theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_rbhImbalance
    (n : ℕ) (rho : XiDivisorSupport) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n
        (reflectedBiHeatFirstDivisorCopy rho) = 0 ↔
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_rbhImbalance_sq]
  have hS : d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility n rho ≠ 0 :=
    ne_of_gt (d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility_pos n rho)
  simp [hS]

/-- Universal extinction of the polarized causal current is exactly FZZ-P information
equilibrium. -/
theorem forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_fzzEquilibrium
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q = 0) ↔
      FZZCigarParityDeningerInformationWardEquilibrium := by
  unfold FZZCigarParityDeningerInformationWardEquilibrium
  constructor <;> intro h q
  · exact (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_fzzForce
      n q).1 (h q)
  · exact (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_fzzForce
      n q).2 (h q)

/-- At every fixed recoil grade, universal extinction of the same causal current is exactly PW-B
partner balance. -/
theorem forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_pwBalanced
    (n k : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q = 0) ↔
      SchwarzschildParikhWilczekBorelPartnerBalancedAtGrade k := by
  unfold SchwarzschildParikhWilczekBorelPartnerBalancedAtGrade
  constructor <;> intro h q
  · exact (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_pwImbalance
      n k q).1 (h q)
  · exact (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_pwImbalance
      n k q).2 (h q)

/-- Universal extinction on canonical first divisor copies is exactly actual RBH
multiplicity-leading balance. -/
theorem forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_firstCopy_eq_zero_iff_rbh
    (n : ℕ) :
    (∀ rho : XiDivisorSupport,
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n
        (reflectedBiHeatFirstDivisorCopy rho) = 0) ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 := by
  constructor <;> intro h rho
  · exact (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_rbhImbalance
      n rho).1 (h rho)
  · exact (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_rbhImbalance
      n rho).2 (h rho)

/-- Any fixed QNM grade and PW recoil grade identify universal polarized-current extinction with
RH through all four route languages. -/
theorem forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q = 0) ↔
      RiemannHypothesis := by
  exact
    (forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_fzzEquilibrium
      n).trans fzzCigarParityDeningerInformationWardEquilibrium_iff_riemannHypothesis

/-- Canonical-first-copy RBH extinction of the polarized current is also exactly RH. -/
theorem forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_firstCopy_eq_zero_iff_rh
    (n : ℕ) :
    (∀ rho : XiDivisorSupport,
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n
        (reflectedBiHeatFirstDivisorCopy rho) = 0) ↔
      RiemannHypothesis := by
  exact
    (forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_firstCopy_eq_zero_iff_rbh
      n).trans riemannHypothesis_iff_reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero.symm

end

end RHTower
