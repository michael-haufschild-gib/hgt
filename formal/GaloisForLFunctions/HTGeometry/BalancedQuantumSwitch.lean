import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Balanced quantum-switch branches

At control weight `p = 1/2`, the two postselected branches in arXiv:2608.25870 are
the normalized sum and difference of the two operation orders.  The odd branch is
exactly one half of the statewise commutator.  This module records that mechanism for
arbitrary bounded linear operations.
-/

namespace HTGeometry

noncomputable section

variable {K E : Type*} [RCLike K]
  [NormedAddCommGroup E] [InnerProductSpace K E]

/-- Even postselected branch of a balanced two-operation quantum switch. -/
def balancedQuantumSwitchEven (A B : E →L[K] E) (psi : E) : E :=
  (2 : K)⁻¹ • ((A * B) psi + (B * A) psi)

/-- Odd postselected branch of a balanced two-operation quantum switch. -/
def balancedQuantumSwitchOdd (A B : E →L[K] E) (psi : E) : E :=
  (2 : K)⁻¹ • ((A * B) psi - (B * A) psi)

/-- Even and odd branches reconstruct the first definite order. -/
theorem balancedQuantumSwitchEven_add_odd
    (A B : E →L[K] E) (psi : E) :
    balancedQuantumSwitchEven A B psi + balancedQuantumSwitchOdd A B psi =
      (A * B) psi := by
  rw [balancedQuantumSwitchEven, balancedQuantumSwitchOdd, ← smul_add]
  rw [show (A * B) psi + (B * A) psi + ((A * B) psi - (B * A) psi) =
      (2 : K) • (A * B) psi by rw [two_smul]; abel]
  rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

/-- Even minus odd reconstructs the reverse definite order. -/
theorem balancedQuantumSwitchEven_sub_odd
    (A B : E →L[K] E) (psi : E) :
    balancedQuantumSwitchEven A B psi - balancedQuantumSwitchOdd A B psi =
      (B * A) psi := by
  rw [balancedQuantumSwitchEven, balancedQuantumSwitchOdd, ← smul_sub]
  rw [show (A * B) psi + (B * A) psi - ((A * B) psi - (B * A) psi) =
      (2 : K) • (B * A) psi by rw [two_smul]; abel]
  rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

/-- The odd balanced ICO branch is half the statewise commutator. -/
theorem balancedQuantumSwitchOdd_eq_half_commutator
    (A B : E →L[K] E) (psi : E) :
    balancedQuantumSwitchOdd A B psi =
      (2 : K)⁻¹ • ((A * B - B * A) psi) := by
  simp [balancedQuantumSwitchOdd]

/-- Odd branch vanishes exactly when the two orders agree on the probe state. -/
theorem balancedQuantumSwitchOdd_eq_zero_iff
    (A B : E →L[K] E) (psi : E) :
    balancedQuantumSwitchOdd A B psi = 0 ↔ (A * B) psi = (B * A) psi := by
  rw [balancedQuantumSwitchOdd]
  simp [sub_eq_zero]

/-- Globally commuting operations have no odd balanced ICO branch on any probe. -/
theorem balancedQuantumSwitchOdd_eq_zero_of_commute
    (A B : E →L[K] E) (hcomm : A * B = B * A) (psi : E) :
    balancedQuantumSwitchOdd A B psi = 0 := by
  rw [balancedQuantumSwitchOdd_eq_zero_iff, hcomm]

/-- Swapping operation order fixes the even branch. -/
theorem balancedQuantumSwitchEven_swap
    (A B : E →L[K] E) (psi : E) :
    balancedQuantumSwitchEven B A psi = balancedQuantumSwitchEven A B psi := by
  simp [balancedQuantumSwitchEven, add_comm]

/-- Swapping operation order negates the odd branch. -/
theorem balancedQuantumSwitchOdd_swap
    (A B : E →L[K] E) (psi : E) :
    balancedQuantumSwitchOdd B A psi = -balancedQuantumSwitchOdd A B psi := by
  simp [balancedQuantumSwitchOdd]
  module

/-- Exact norm conversion between commutator response and odd ICO branch. -/
theorem norm_commutator_apply_eq_two_mul_norm_balancedQuantumSwitchOdd
    (A B : E →L[K] E) (psi : E) :
    ‖((A * B - B * A) : E →L[K] E) psi‖ =
      2 * ‖balancedQuantumSwitchOdd A B psi‖ := by
  rw [balancedQuantumSwitchOdd_eq_half_commutator, norm_smul]
  have htwo : ‖(2 : K)‖ = 2 := by norm_num
  rw [norm_inv, htwo]
  norm_num
  ring

/-- Squared commutator response is four times odd-branch intensity. -/
theorem norm_commutator_apply_sq_eq_four_mul_norm_balancedQuantumSwitchOdd_sq
    (A B : E →L[K] E) (psi : E) :
    ‖((A * B - B * A) : E →L[K] E) psi‖ ^ (2 : ℕ) =
      4 * ‖balancedQuantumSwitchOdd A B psi‖ ^ (2 : ℕ) := by
  rw [norm_commutator_apply_eq_two_mul_norm_balancedQuantumSwitchOdd]
  ring

end

end HTGeometry
