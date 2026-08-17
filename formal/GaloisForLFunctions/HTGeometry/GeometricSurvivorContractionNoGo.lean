import Mathlib.Tactic

/-!
# Strict weighted decay does not force finite absorption

A positive geometric observation can contract by a fixed factor along an
infinite deterministic orbit. Thus strict decay in a weighted observation,
without a lower-bound faithfulness condition, does not certify finite
absorption.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The deterministic forward orbit used by the countermodel. -/
def survivorAdvance (n : ℕ) : ℕ := n + 1

/-- Positive geometric weight attached to a point on the orbit. -/
def geometricSurvivalWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

@[simp]
theorem survivorAdvance_iterate (m n : ℕ) :
    (survivorAdvance^[m]) n = n + m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, survivorAdvance]
      omega

theorem geometricSurvivalWeight_pos (n : ℕ) : 0 < geometricSurvivalWeight n := by
  exact pow_pos (by positivity) _

theorem geometricSurvivalWeight_advance (n : ℕ) :
    geometricSurvivalWeight (survivorAdvance n) = geometricSurvivalWeight n / 2 := by
  change (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n / 2
  rw [pow_succ]
  ring

theorem geometricSurvivalWeight_strictly_decreases (n : ℕ) :
    geometricSurvivalWeight (survivorAdvance n) < geometricSurvivalWeight n := by
  rw [geometricSurvivalWeight_advance]
  nlinarith [geometricSurvivalWeight_pos n]

theorem survivorAdvance_orbit_ne_zero (m : ℕ) :
    (survivorAdvance^[m]) 1 ≠ 0 := by
  rw [survivorAdvance_iterate]
  omega

/-- **Faithfulness no-go.** A uniformly strictly contracting positive weight can coexist with an
orbit that never reaches the terminal state `0`. -/
theorem strict_weight_decay_not_finite_absorption :
    (∀ n, 0 < geometricSurvivalWeight n) ∧
      (∀ n, geometricSurvivalWeight (survivorAdvance n) = geometricSurvivalWeight n / 2) ∧
      (∀ n, geometricSurvivalWeight (survivorAdvance n) < geometricSurvivalWeight n) ∧
      ∀ m, (survivorAdvance^[m]) 1 ≠ 0 := by
  exact ⟨geometricSurvivalWeight_pos, geometricSurvivalWeight_advance,
    geometricSurvivalWeight_strictly_decreases, survivorAdvance_orbit_ne_zero⟩

end

end GaloisForLFunctions.HTGeometry
