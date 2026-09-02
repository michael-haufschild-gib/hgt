import GaloisForLFunctions.HTGeometry.TowerWeightedDegree

/-!
# Separated weights for normalized cascade states

For a cascade of depth `n`, the weights `(n² + 1)^ℓ` dominate the complete accumulated loss from
all lower levels.  This is the exact numerical separation condition used by the normalized-state
recursion in the algebraic product-cascade observability proof.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- Rapidly increasing weights used for a cascade of depth `n`. -/
def cascadeSeparationWeight (n j : ℕ) : ℕ := (n * n + 1) ^ j

/-- **The geometric cascade weights dominate the complete accumulated lower-level loss.** -/
theorem sum_weighted_cascadeSeparationWeight_lt (n ℓ : ℕ) (hℓ : ℓ ≤ n) :
    (∑ i ∈ Finset.Ico 2 ℓ, (i - 1) * cascadeSeparationWeight n i)
      < cascadeSeparationWeight n ℓ := by
  induction ℓ with
  | zero => simp [cascadeSeparationWeight]
  | succ ℓ ih =>
      by_cases hsmall : ℓ ≤ 1
      · interval_cases ℓ <;>
        simp [cascadeSeparationWeight]
      · have htwo : 2 ≤ ℓ := by omega
        rw [Finset.sum_Ico_succ_top htwo]
        have hprev :
            (∑ i ∈ Finset.Ico 2 ℓ, (i - 1) * cascadeSeparationWeight n i)
              < cascadeSeparationWeight n ℓ := ih (by omega)
        have hbase : ℓ < n * n + 1 := by nlinarith
        have hppos : 0 < cascadeSeparationWeight n ℓ := by
          exact pow_pos (by omega) _
        have hmul : ℓ * cascadeSeparationWeight n ℓ
            < (n * n + 1) * cascadeSeparationWeight n ℓ := by
          exact Nat.mul_lt_mul_of_pos_right hbase hppos
        calc
          (∑ i ∈ Finset.Ico 2 ℓ, (i - 1) * cascadeSeparationWeight n i)
                + (ℓ - 1) * cascadeSeparationWeight n ℓ
              < cascadeSeparationWeight n ℓ
                + (ℓ - 1) * cascadeSeparationWeight n ℓ :=
            Nat.add_lt_add_right hprev _
          _ = (1 + (ℓ - 1)) * cascadeSeparationWeight n ℓ := by
            rw [Nat.add_mul, one_mul]
          _ = ℓ * cascadeSeparationWeight n ℓ := by
            congr 1
            omega
          _ < (n * n + 1) * cascadeSeparationWeight n ℓ := hmul
          _ = cascadeSeparationWeight n (ℓ + 1) := by
            rw [cascadeSeparationWeight, cascadeSeparationWeight, pow_succ, mul_comm]

end GaloisForLFunctions.HTGeometry
