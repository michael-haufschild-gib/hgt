import GaloisForLFunctions.ArithmeticDefectRigidity.CompleteWienerPairingsFollowTheCommonCofactorLimit
import GaloisForLFunctions.ArithmeticOrientationTheory.WienerCoefficientEvaluation

/-!
# Complete Wiener source rows respect dilation

Finite source-cell evaluation is continuous in the full Wiener kernel.
Multiplication by a point mass is exactly integer floor dilation, including
infinite-support kernels.
-/

noncomputable section
set_option autoImplicit false
open Finset

open RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The finite-cell source action is a continuous linear functional of its Wiener kernel. -/
def sourceCellLinear (ε : SubcriticalDamping) (n : ℕ) : WienerAlgebraAt (1 / 2) →L[ℂ] ℂ :=
  ∑ j ∈ Icc 1 n, (pmPowerDampedCenteredDivisorPrefix ε (n / j) : ℂ) •
    coefficientLinear (1 / 2) j

theorem sourceCellLinear_apply (ε : SubcriticalDamping) (n : ℕ)
    (a : WienerAlgebraAt (1 / 2)) : sourceCellLinear ε n a = complexWienerRow ε a n := by
  simp only [sourceCellLinear, _root_.sum_apply, smul_apply,
    coefficientLinear_apply, smul_eq_mul, complexWienerRow, mul_comm]

theorem complexWienerRow_pointMass (ε : SubcriticalDamping) (m n : ℕ) :
    complexWienerRow ε (pointMass m) n = (pmPowerDampedCenteredDivisorPrefix ε (n / m) : ℂ) := by
  unfold complexWienerRow
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [toFn_pointMass, pointMassFn_apply, Nat.div_zero,
      ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      Complex.ofReal_zero]
    apply sum_eq_zero
    intro j hj
    rw [if_neg (by have := (mem_Icc.mp hj).1; omega), zero_mul]
  · by_cases hmn : m ≤ n
    · rw [sum_eq_single m]
      · simp only [toFn_pointMass, pointMassFn_apply, hm.ne', ne_eq, not_false_eq_true,
          and_self, if_true, one_mul]
      · intro j hj hjm
        simp only [toFn_pointMass, pointMassFn_apply,
          if_neg (show ¬ (j ≠ 0 ∧ j = m) from fun h => hjm h.2), zero_mul]
      · intro hnot
        exact (hnot (mem_Icc.mpr ⟨hm, hmn⟩)).elim
    · rw [Nat.div_eq_of_lt (lt_of_not_ge hmn),
        ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
        Complex.ofReal_zero]
      apply sum_eq_zero
      intro j hj
      have hjm : j ≠ m := by have := (mem_Icc.mp hj).2; omega
      simp only [toFn_pointMass, pointMassFn_apply,
        if_neg (show ¬ (j ≠ 0 ∧ j = m) from fun h => hjm h.2), zero_mul]

theorem sourceCellLinear_pointMass (ε : SubcriticalDamping) (n m : ℕ) :
    sourceCellLinear ε n (pointMass m) =
      (pmPowerDampedCenteredDivisorPrefix ε (n / m) : ℂ) := by
  rw [sourceCellLinear_apply, complexWienerRow_pointMass]

/-- Multiplication by a point mass is exactly floor dilation of every complete source row. -/
theorem complexWienerRow_mul_pointMass (ε : SubcriticalDamping)
    (a : WienerAlgebraAt (1 / 2)) (p n : ℕ) :
    complexWienerRow ε (a * pointMass p) n = complexWienerRow ε a (n / p) := by
  have hleft := (sourceCellLinear ε n).hasSum ((hasSum_pointMass a).mul_right (pointMass p))
  have hright := (sourceCellLinear ε (n / p)).hasSum (hasSum_pointMass a)
  simp only [smul_mul_assoc, map_smul, pointMass_mul, sourceCellLinear_apply,
    complexWienerRow_pointMass] at hleft hright
  apply HasSum.unique hleft
  convert hright using 1
  funext j
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm p j]

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.complexWienerRow_mul_pointMass

