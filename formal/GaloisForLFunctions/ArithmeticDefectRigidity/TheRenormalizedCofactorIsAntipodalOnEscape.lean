import GaloisForLFunctions.ArithmeticDefectRigidity.TheForcingSplitsIntoAPowerAndAnAdmittedRemainder
import GaloisForLFunctions.ArithmeticDefectRigidity.ForcingScaleSeparation

/-!
# The signed residual after the forcing power is paid

The actual cofactor residual has pairing `-E + O(√E)` with the receiver. Thus every escaping
receiver has normalized residual pairing tending to `-1`. This retains a signed constraint
after subtracting the forcing power; it does not exclude that constraint.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The actual receiver's signed pairing with its power-subtracted cofactor residual. -/
def renormalizedCofactorWork (ε : ℝ) (T : ℕ) : ℝ :=
  pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (renormalizedCofactor ε)

/-- All failure of exact antipodality is carried by the paid forcing remainder. -/
theorem receiverEnergy_add_renormalizedCofactorWork_eq (ε : SubcriticalDamping) (T : ℕ) :
    dampedMobiusEnergy ε T + renormalizedCofactorWork ε T =
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (forcingRemainder ε) := by
  have hE : dampedMobiusEnergy ε T =
      pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) ^ 2 := by
    rw [pronicNorm_centeredPrefix, Real.sq_sqrt (dampedMobiusEnergy_nonneg ε T)]
  rw [hE]
  simp only [renormalizedCofactorWork, pronicPairing, pronicNorm_sq, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hid : pmPowerDampedCenteredDivisorPrefix ε n + renormalizedCofactor ε n =
      forcingRemainder ε n := by
    cases n with
    | zero => simp only [mem_Icc] at hn; omega
    | succ n => exact receiver_add_renormalizedCofactor_eq ε n
  rw [← hid]
  ring

/-- The signed failure of antipodality costs at most the paid remainder norm times `√E`. -/
theorem abs_receiverEnergy_add_renormalizedCofactorWork_le (ε : SubcriticalDamping) (T : ℕ) :
    |dampedMobiusEnergy ε T + renormalizedCofactorWork ε T| ≤
      Real.sqrt (dampedMobiusEnergy ε T) * forcingRemainderBudget ε := by
  rw [receiverEnergy_add_renormalizedCofactorWork_eq]
  have hp := sum_mul_div_le_pronicNorm T
    (pmPowerDampedCenteredDivisorPrefix ε) (forcingRemainder ε)
  have hn := sum_mul_div_le_pronicNorm T
    (pmPowerDampedCenteredDivisorPrefix ε) (fun n => -forcingRemainder ε n)
  rw [pronicNorm_neg] at hn
  have heq : (∑ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix (ε : ℝ) n *
      -forcingRemainder ε n / ((n : ℝ) * ((n : ℝ) + 1))) =
      -pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (forcingRemainder ε) := by
    simp only [pronicPairing, mul_neg, neg_div, sum_neg_distrib]
  rw [heq, pronicNorm_centeredPrefix] at hn
  rw [pronicNorm_centeredPrefix] at hp
  change pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (forcingRemainder ε) ≤ _ at hp
  have hcs : |pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (forcingRemainder ε)| ≤
      Real.sqrt (dampedMobiusEnergy ε T) * pronicNorm T (forcingRemainder ε) :=
    abs_le.mpr ⟨by linarith, hp⟩
  exact hcs.trans (mul_le_mul_of_nonneg_left (pronicNorm_forcingRemainder_le ε T)
    (Real.sqrt_nonneg _))

/-- Squared antipodal error is linear in receiver energy, with an explicit fixed coefficient. -/
theorem receiverEnergy_add_renormalizedCofactorWork_sq_le (ε : SubcriticalDamping) (T : ℕ) :
    (dampedMobiusEnergy ε T + renormalizedCofactorWork ε T) ^ 2 ≤
      dampedMobiusEnergy ε T * forcingRemainderBudget ε ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (abs_receiverEnergy_add_renormalizedCofactorWork_le ε T) 2
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (dampedMobiusEnergy_nonneg ε T)] using h

/-- The normalized signed pairing has a quantitative distance from `-1`. -/
theorem normalized_renormalizedCofactorWork_error_le (ε : SubcriticalDamping) (T : ℕ) :
    (renormalizedCofactorWork ε (T + 1) / dampedMobiusEnergy ε (T + 1) + 1) ^ 2 ≤
      forcingRemainderBudget ε ^ 2 / dampedMobiusEnergy ε (T + 1) := by
  have hE : dampedMobiusEnergy ε (T + 1) ≠ 0 := (receiverEnergy_succ_pos ε T).ne'
  calc _ = (dampedMobiusEnergy ε (T + 1) + renormalizedCofactorWork ε (T + 1)) ^ 2 /
        dampedMobiusEnergy ε (T + 1) ^ 2 := by field_simp; ring
    _ ≤ (dampedMobiusEnergy ε (T + 1) * forcingRemainderBudget ε ^ 2) /
        dampedMobiusEnergy ε (T + 1) ^ 2 :=
      div_le_div_of_nonneg_right (receiverEnergy_add_renormalizedCofactorWork_sq_le ε (T + 1))
        (sq_nonneg _)
    _ = _ := by field_simp

/-- Every escaping actual receiver has the same antipodal normalized cofactor pairing. -/
theorem admits_or_renormalizedCofactorWork_is_antipodal (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      Tendsto (fun T => (renormalizedCofactorWork ε T / dampedMobiusEnergy ε T + 1) ^ 2)
        atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr (squeeze_zero' (Filter.Eventually.of_forall fun T => sq_nonneg _) ?_
      (tendsto_const_nhds.div_atTop hE))
    filter_upwards [eventually_ge_atTop 1] with T hT
    cases T with
    | zero => omega
    | succ T => exact normalized_renormalizedCofactorWork_error_le ε T

end GaloisForLFunctions.ArithmeticDefectRigidity
