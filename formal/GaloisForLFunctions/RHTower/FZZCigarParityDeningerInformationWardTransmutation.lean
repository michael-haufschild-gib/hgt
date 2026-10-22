import GaloisForLFunctions.RHTower.FZZCigarParityReflectedFermiInformationGradientFlow
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorGaugeWardIdentity
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# FZZ information force as a Deninger displacement Ward charge

The nonlinear reflected Fermi information force and the Deninger reflect-gauge commutator are the
same oriented divisor charge up to a strictly positive source multiplier on the open strip.
-/

open Complex MeasureTheory Set InformationTheory
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Positive conversion factor from critical displacement to nonlinear Fermi information force. -/
def fzzCigarParityDeningerInformationWardMultiplier (sigma : ℝ) : ℝ :=
  if sigma = 1 / 2 then 1
  else fzzCigarParityReflectedFermiInformationForce sigma / (2 * sigma - 1)

theorem fzzCigarParityReflectedFermiInformationForce_eq_centered_mul_wardMultiplier
    (sigma : ℝ) :
    fzzCigarParityReflectedFermiInformationForce sigma =
      (2 * sigma - 1) * fzzCigarParityDeningerInformationWardMultiplier sigma := by
  by_cases hcenter : sigma = 1 / 2
  · subst sigma
    norm_num [fzzCigarParityDeningerInformationWardMultiplier,
      fzzCigarParityReflectedFermiInformationForce_half]
  · rw [fzzCigarParityDeningerInformationWardMultiplier, if_neg hcenter]
    have hdenom : 2 * sigma - 1 ≠ 0 := by
      intro hz
      apply hcenter
      linarith
    field_simp

/-- Strict positivity makes the information/Ward conversion orientation-preserving. -/
theorem fzzCigarParityDeningerInformationWardMultiplier_pos
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) :
    0 < fzzCigarParityDeningerInformationWardMultiplier sigma := by
  by_cases hcenter : sigma = 1 / 2
  · simp [fzzCigarParityDeningerInformationWardMultiplier, hcenter]
  · rw [fzzCigarParityDeningerInformationWardMultiplier, if_neg hcenter]
    rcases lt_or_gt_of_ne hcenter with hlt | hgt
    · exact div_pos_of_neg_of_neg
        (fzzCigarParityReflectedFermiInformationForce_neg_of_lt_half h0 hlt)
        (by linarith)
    · exact div_pos
        (fzzCigarParityReflectedFermiInformationForce_pos_of_half_lt hgt h1)
        (by linarith)

/-- Cup-traced Deninger reflect-gauge commutator at one divisor copy. -/
def fzzCigarParityDeningerReflectGaugeWardCharge (q : XiZeroCopy) : ℂ :=
  deningerDivisorCupTrace (Finsupp.single q 1)
    (deningerDivisorTheta (deningerDivisorReflectGauge (Finsupp.single q 1)) -
      deningerDivisorReflectGauge (deningerDivisorTheta (Finsupp.single q 1)))

/-- The reflect-gauge Ward charge is exactly signed critical displacement. -/
theorem fzzCigarParityDeningerReflectGaugeWardCharge_eq (q : XiZeroCopy) :
    fzzCigarParityDeningerReflectGaugeWardCharge q =
      ((1 - 2 * (deningerDivisorThetaEigen q).re : ℝ) : ℂ) := by
  rw [fzzCigarParityDeningerReflectGaugeWardCharge,
    deningerDivisor_antilinearGauge_ward, deningerDivisorReflectGauge_diag, mul_one]
  have hsum := deningerDivisorThetaEigen_add_reflect q
  have hreflect :
      deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) =
        1 - deningerDivisorThetaEigen q := by
    linear_combination hsum
  rw [hreflect]
  apply Complex.ext <;> simp
  ring

/-- Every divisor-flow eigenvalue is a literal source-first FZZ parity-Mellin mode. -/
theorem fzzCigarParityMellinMode_deningerDivisorThetaEigen (q : XiZeroCopy) :
    FZZCigarParityMellinMode (deningerDivisorThetaEigen q) := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  exact (fzzCigarParityMellin_eq_zero_iff_xi_eq_zero h0 h1).2
    (xi_deningerDivisorThetaEigen_eq_zero q)

/-- Exact cross-route transmutation: nonlinear Fermi force is a positive multiple of the negative
Deninger reflect-gauge Ward charge. -/
theorem fzzCigarParityInformationForce_eq_neg_wardMultiplier_mul_deningerCharge
    (q : XiZeroCopy) :
    ((fzzCigarParityReflectedFermiInformationForce
      (deningerDivisorThetaEigen q).re : ℝ) : ℂ) =
      -(fzzCigarParityDeningerInformationWardMultiplier
          (deningerDivisorThetaEigen q).re : ℂ) *
        fzzCigarParityDeningerReflectGaugeWardCharge q := by
  rw [fzzCigarParityReflectedFermiInformationForce_eq_centered_mul_wardMultiplier,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  push_cast
  ring

theorem fzzCigarParityDeningerReflectGaugeWardCharge_eq_zero_iff
    (q : XiZeroCopy) :
    fzzCigarParityDeningerReflectGaugeWardCharge q = 0 ↔
      (deningerDivisorThetaEigen q).re = 1 / 2 := by
  rw [fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp only [ofReal_eq_zero]
  constructor <;> intro h <;> linarith

/-- Local reflect-gauge equivariance is exactly critical-line placement. -/
theorem deningerDivisorReflectGauge_comm_iff_re_eq_half (q : XiZeroCopy) :
    deningerDivisorTheta (deningerDivisorReflectGauge (Finsupp.single q 1)) =
        deningerDivisorReflectGauge (deningerDivisorTheta (Finsupp.single q 1)) ↔
      (deningerDivisorThetaEigen q).re = 1 / 2 := by
  constructor
  · intro hcomm
    exact deningerDivisorThetaEigen_re_eq_half_of_antilinearGauge
      deningerDivisorReflectGauge q hcomm (by
        rw [deningerDivisorReflectGauge_diag]
        exact one_ne_zero)
  · intro hre
    rw [← sub_eq_zero]
    rw [deningerDivisorReflectGauge_defect]
    have hadd := Complex.add_conj (deningerDivisorThetaEigen q)
    rw [hre] at hadd
    have hconj :
        (starRingEnd ℂ) (deningerDivisorThetaEigen q) =
          1 - deningerDivisorThetaEigen q := by
      have hone : deningerDivisorThetaEigen q +
          (starRingEnd ℂ) (deningerDivisorThetaEigen q) = 1 := by
        rw [hadd]
        norm_num
      linear_combination hone
    have hfactor :
        deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) -
          (starRingEnd ℂ) (deningerDivisorThetaEigen q) = 0 := by
      rw [hconj]
      linear_combination deningerDivisorThetaEigen_add_reflect q
    rw [hfactor, zero_mul, Finsupp.single_zero]

/-- Per-copy FZZ information equilibrium and Deninger reflect-gauge equivariance are identical. -/
theorem fzzCigarParityInformationForce_eq_zero_iff_deningerReflectGauge_comm
    (q : XiZeroCopy) :
    fzzCigarParityReflectedFermiInformationForce
        (deningerDivisorThetaEigen q).re = 0 ↔
      deningerDivisorTheta (deningerDivisorReflectGauge (Finsupp.single q 1)) =
        deningerDivisorReflectGauge (deningerDivisorTheta (Finsupp.single q 1)) := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  change fzzCigarParityReflectedFermiInformationForce (q.1 : ℂ).re = 0 ↔ _
  rw [fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1,
    deningerDivisorReflectGauge_comm_iff_re_eq_half]
  rfl

/-- Universal shared FZZ-information/Deninger-Ward equilibrium over the actual Xi divisor. -/
def FZZCigarParityDeningerInformationWardEquilibrium : Prop :=
  ∀ q : XiZeroCopy,
    fzzCigarParityReflectedFermiInformationForce
      (deningerDivisorThetaEigen q).re = 0

theorem fzzCigarParityDeningerInformationWardEquilibrium_iff_reflectGaugeEquivariant :
    FZZCigarParityDeningerInformationWardEquilibrium ↔
      ∀ q : XiZeroCopy,
        deningerDivisorTheta (deningerDivisorReflectGauge (Finsupp.single q 1)) =
          deningerDivisorReflectGauge (deningerDivisorTheta (Finsupp.single q 1)) := by
  constructor <;> intro h q
  · exact (fzzCigarParityInformationForce_eq_zero_iff_deningerReflectGauge_comm q).mp (h q)
  · exact (fzzCigarParityInformationForce_eq_zero_iff_deningerReflectGauge_comm q).mpr (h q)

/-- Exact shared Ward endpoint: universal cancellation is RH-strength. -/
theorem fzzCigarParityDeningerInformationWardEquilibrium_iff_riemannHypothesis :
    FZZCigarParityDeningerInformationWardEquilibrium ↔ RiemannHypothesis := by
  constructor
  · intro heq
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
    exact (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).mp (heq q)
  · intro hRH q
    apply (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff
      (xi_divisor_support_re_mem_open_unit q.1).1
      (xi_divisor_support_re_mem_open_unit q.1).2).2
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have him := congrArg Complex.im ht
    simp [xiSpectralPoint] at him
    linarith

theorem riemannHypothesis_iff_fzzCigarParityDeningerInformationWardEquilibrium :
    RiemannHypothesis ↔ FZZCigarParityDeningerInformationWardEquilibrium :=
  fzzCigarParityDeningerInformationWardEquilibrium_iff_riemannHypothesis.symm

end

end RHTower
