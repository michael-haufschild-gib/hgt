import GaloisForLFunctions.ArithmeticDefectRigidity.TheForcingDominatesTheReceiver
import GaloisForLFunctions.ArithmeticCompensationTheory.TheReceiverEnergyEscapesToTheHorizon
import GaloisForLFunctions.BezoutValuationIncidence.PredictableMartingaleDecompositionAndCovarianceCancellationBridge

/-!
# Fixed successors disappear from escaping profiles

The actual damped divisor response lies in `[0,1]`, as does its density. Consequently the
centered prefix has increments bounded by one. Translating it by `k` cells costs at most `k²`
in pronic energy, uniformly in the horizon.

If receiver energy escapes, every fixed successor translation therefore becomes the identity
after normalization. More generally, a moving translation disappears whenever its squared
length is negligible relative to receiver energy. A defect extraction retaining only fixed
translations cannot retain their arithmetic selectivity.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

private theorem density_le_one (ε : SubcriticalDamping) :
    (pmPowerDampedDivisorDensity (ε : ℝ)).re ≤ 1 := by
  have h := sum_Icc_rpow_le_realZetaSeries ε.property.1 1
  have hZ : 1 ≤ realZetaSeries (1 + (ε : ℝ)) := by simpa using h
  rw [pmPowerDampedDivisorDensity_re_eq ε.property.1]
  exact (div_le_one (realZetaSeries_pos (by linarith [ε.property.1]))).mpr hZ

/-- The centered arithmetic response has absolute value at most one. -/
theorem abs_centeredResponse_le_one (ε : SubcriticalDamping) (n : ℕ) :
    |pmPowerDampedCenteredDivisorCoeff ε n| ≤ 1 := by
  have hc0 := pmPowerDampedDivisorCoeff_nonneg ε.property.1.le n
  have hc1 := pmPowerDampedDivisorCoeff_le_one ε.property.1.le n
  have hm0 := pmPowerDampedDivisorDensity_re_pos ε.property.1
  have hm1 := density_le_one ε
  unfold pmPowerDampedCenteredDivisorCoeff
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A translation by `k` cells changes the actual prefix by at most `k`. -/
theorem abs_receiver_shift_sub_le (ε : SubcriticalDamping) (n k : ℕ) :
    |pmPowerDampedCenteredDivisorPrefix ε (n + k) -
      pmPowerDampedCenteredDivisorPrefix ε n| ≤ (k : ℝ) := by
  induction k with
  | zero => simp only [Nat.add_zero, sub_self, abs_zero, Nat.cast_zero, le_refl]
  | succ k ih =>
    rw [Nat.add_succ, Nat.succ_eq_add_one, pmPowerDampedCenteredDivisorPrefix_succ]
    have he : pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n + k) +
        pmPowerDampedCenteredDivisorCoeff (ε : ℝ) (n + k + 1) -
        pmPowerDampedCenteredDivisorPrefix (ε : ℝ) n =
        (pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n + k) -
          pmPowerDampedCenteredDivisorPrefix (ε : ℝ) n) +
        pmPowerDampedCenteredDivisorCoeff (ε : ℝ) (n + k + 1) := by ring
    rw [he, Nat.cast_add, Nat.cast_one]
    exact (abs_add _ _).trans (add_le_add ih (abs_centeredResponse_le_one ε _))

/-- The energy of the actual source's displacement by a successor translation. -/
def successorDisplacementEnergy (ε : ℝ) (k T : ℕ) : ℝ :=
  pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε (n + k) -
    pmPowerDampedCenteredDivisorPrefix ε n) ^ 2

theorem successorDisplacementEnergy_nonneg (ε : ℝ) (k T : ℕ) :
    0 ≤ successorDisplacementEnergy ε k T := sq_nonneg _

/-- Successor displacement has a horizon-independent quadratic budget. -/
theorem successorDisplacementEnergy_le (ε : SubcriticalDamping) (k T : ℕ) :
    successorDisplacementEnergy ε k T ≤ (k : ℝ) ^ 2 := by
  have hsq : ∀ n : ℕ,
      (pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n + k) -
        pmPowerDampedCenteredDivisorPrefix (ε : ℝ) n) ^ 2 ≤ (k : ℝ) ^ 2 := by
    intro n
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_receiver_shift_sub_le ε n k) 2
  have hone : pronicNorm T (fun _ => 1) ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (pronicNorm_nonneg T (fun _ => 1)) (pronicNorm_one_le T) 2
  calc successorDisplacementEnergy ε k T
      = ∑ n ∈ Icc 1 T, (pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n + k) -
          pmPowerDampedCenteredDivisorPrefix (ε : ℝ) n) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) := pronicNorm_sq _ _
    _ ≤ ∑ n ∈ Icc 1 T, (k : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      sum_le_sum fun n _ => div_le_div_of_nonneg_right (hsq n) (by positivity)
    _ = (k : ℝ) ^ 2 * pronicNorm T (fun _ => 1) ^ 2 := by
      rw [pronicNorm_sq, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ (k : ℝ) ^ 2 := by nlinarith [sq_nonneg (k : ℝ)]

/-- Every fixed successor is invisible to an escaping normalized receiver. -/
theorem admits_or_fixed_successors_disappear (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ k : ℕ,
      Tendsto (fun T => successorDisplacementEnergy ε k T / dampedMobiusEnergy ε T)
        atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun k => squeeze_zero
      (fun T => div_nonneg (successorDisplacementEnergy_nonneg ε k T)
        (dampedMobiusEnergy_nonneg ε T))
      (fun T => div_le_div_of_nonneg_right (successorDisplacementEnergy_le ε k T)
        (dampedMobiusEnergy_nonneg ε T)) ?_
    exact tendsto_const_nhds.div_atTop hE

/-- The same disappearance holds on every translation scale below the energy square root. -/
theorem admits_or_moving_successors_disappear (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ k : ℕ → ℕ,
      Tendsto (fun T => (k T : ℝ) ^ 2 / dampedMobiusEnergy ε T) atTop (𝓝 0) →
      Tendsto (fun T => successorDisplacementEnergy ε (k T) T / dampedMobiusEnergy ε T)
        atTop (𝓝 0) := by
  refine Or.inr fun k hk => squeeze_zero
    (fun T => div_nonneg (successorDisplacementEnergy_nonneg ε (k T) T)
      (dampedMobiusEnergy_nonneg ε T))
    (fun T => div_le_div_of_nonneg_right (successorDisplacementEnergy_le ε (k T) T)
      (dampedMobiusEnergy_nonneg ε T)) hk

end GaloisForLFunctions.ArithmeticDefectRigidity
