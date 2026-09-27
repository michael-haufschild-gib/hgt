import GaloisForLFunctions.RHTower.LogarithmicReconstructionAction
import GaloisForLFunctions.RHTower.LogarithmicMobiusShortReconstruction

/-!
# Exact continuous tail symmetry of the arithmetic action

Two perturbations supported beyond the square-root cutoff cannot interact
before terminal time. The Möbius stationary action is consequently
unchanged by every real deformation of its long coefficients. This is an
exact symmetry of the finite source action, not a bound on its short part.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def logarithmicLongTail (U : ℕ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if U < n then v n else 0

def logarithmicMobiusHeadExtension (U : ℕ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else v n

theorem logarithmicMobiusHeadExtension_eq_mobius_add_longTail (U : ℕ) (v : ℕ → ℝ) :
    logarithmicMobiusHeadExtension U v = fun n => (ArithmeticFunction.moebius n : ℝ) +
      logarithmicLongTail U (fun n => v n - (ArithmeticFunction.moebius n : ℝ)) n := by
  funext n
  by_cases hn : n ≤ U
  · simp [logarithmicMobiusHeadExtension, logarithmicLongTail, hn, not_lt.mpr hn]
  · simp [logarithmicMobiusHeadExtension, logarithmicLongTail, hn, Nat.lt_of_not_ge hn]

theorem continuous_logarithmicMobiusHeadExtension_line (U : ℕ) (v w : ℕ → ℝ) :
    Continuous (fun z : ℝ => logarithmicMobiusHeadExtension U (fun n => v n + z * w n)) := by
  apply continuous_pi
  intro n
  by_cases hn : n ≤ U
  · simpa only [logarithmicMobiusHeadExtension, if_pos hn] using
      (continuous_const : Continuous (fun _ : ℝ => (ArithmeticFunction.moebius n : ℝ)))
  · simp only [logarithmicMobiusHeadExtension, if_neg hn]
    fun_prop

theorem logarithmicWeightedDilation_longTail_pair_eq_zero (U : ℕ)
    (v w : ℕ → ℝ) (f : ℝ → ℝ) {T : ℝ} (hU : ⌊Real.exp T⌋₊ < (U + 1) ^ 2) :
    logarithmicWeightedDilation (logarithmicLongTail U v)
      (logarithmicWeightedDilation (logarithmicLongTail U w) f) T = 0 := by
  rw [logarithmicWeightedDilation_comp]
  unfold logarithmicWeightedDilation
  apply Finset.sum_eq_zero
  intro n hn
  have hz : (∑ x ∈ n.divisorsAntidiagonal,
      logarithmicLongTail U v x.1 * logarithmicLongTail U w x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases ha : U < x.1
    · have hb : ¬ U < x.2 := by
        intro hb
        have hprod : (U + 1) ^ 2 ≤ n := by
          rw [pow_two, ← (Nat.mem_divisorsAntidiagonal.mp hx).1]
          exact Nat.mul_le_mul (Nat.succ_le_of_lt ha) (Nat.succ_le_of_lt hb)
        exact (not_le_of_gt hU) (hprod.trans (Finset.mem_Icc.mp hn).2)
      simp [logarithmicLongTail, hb]
    · simp [logarithmicLongTail, ha]
  dsimp only
  rw [hz, zero_mul]

theorem logarithmicWeightedDilation_halfTail_pair_eq_zero
    (v w : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation (logarithmicLongTail ⌊Real.exp (T / 2)⌋₊ v)
      (logarithmicWeightedDilation (logarithmicLongTail ⌊Real.exp (T / 2)⌋₊ w) f) T = 0 :=
  logarithmicWeightedDilation_longTail_pair_eq_zero _ v w f
    (floor_exp_lt_succ_floor_exp_half_sq T)

theorem logarithmicReconstructionAction_halfTail (v : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) +
        logarithmicLongTail ⌊Real.exp (T / 2)⌋₊ v n) f T =
          logarithmicMobiusInverse f T := by
  rw [logarithmicReconstructionAction_mobius_add,
    logarithmicWeightedDilation_halfTail_pair_eq_zero, sub_zero]

theorem logarithmicReconstructionAction_halfTail_line
    (v : ℕ → ℝ) (f : ℝ → ℝ) (T z : ℝ) :
    logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) +
        z * logarithmicLongTail ⌊Real.exp (T / 2)⌋₊ v n) f T =
          logarithmicMobiusInverse f T := by
  rw [logarithmicReconstructionAction_mobius_line,
    logarithmicWeightedDilation_halfTail_pair_eq_zero, mul_zero, sub_zero]

/-- Arbitrary real translations of the tail parameter preserve the action. -/
theorem logarithmicReconstructionAction_halfTail_translation
    (v : ℕ → ℝ) (f : ℝ → ℝ) (T q z : ℝ) :
    logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) +
        (q + z) * logarithmicLongTail ⌊Real.exp (T / 2)⌋₊ v n) f T =
      logarithmicReconstructionAction
        (fun n => (ArithmeticFunction.moebius n : ℝ) +
          q * logarithmicLongTail ⌊Real.exp (T / 2)⌋₊ v n) f T := by
  rw [logarithmicReconstructionAction_halfTail_line,
    logarithmicReconstructionAction_halfTail_line]

/-- Only the coefficients through the square-root cutoff determine the
stationary value; all later coefficients are arbitrary real numbers. -/
theorem logarithmicReconstructionAction_mobiusHeadExtension
    (v : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicReconstructionAction
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ v) f T =
        logarithmicMobiusInverse f T := by
  rw [logarithmicMobiusHeadExtension_eq_mobius_add_longTail,
    logarithmicReconstructionAction_halfTail]

end RHTower
