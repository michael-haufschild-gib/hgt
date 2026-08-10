import GaloisForLFunctions.RHTower.DeningerAbelianTelescope

/-!
# The Abel average of a bounded sequence

Because the Abel increments are a probability weight, averaging any bounded sequence against them
converges absolutely, and subtracting the limit candidate can be done inside the sum:

`∑ b_n w_σ(n) - S = ∑ (b_n - S) w_σ(n)`.

This is the reduction that makes the Abelian theorem an `ε`-argument: the right-hand side is small
because the tail terms are small and the weight is a probability weight, while the head vanishes
as `σ ↓ 0`.

* `deningerAbelAverage_summable` : bounded sequences average absolutely.
* `deningerAbelAverage_sub` : **the limit candidate can be subtracted inside the sum.**
-/

namespace RHTower

open Filter Topology

noncomputable section

/-- Averaging a bounded sequence against the Abel weight converges absolutely. -/
theorem deningerAbelAverage_summable {b : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |b n| ≤ C) {σ : ℝ}
    (hσ : 0 < σ) : Summable fun n : ℕ => b n * deningerAbelWeight σ n := by
  have hw := (deningerAbelWeight_hasSum_one hσ).summable
  refine Summable.of_norm_bounded (g := fun n => C * deningerAbelWeight σ n)
    (hw.mul_left C) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (deningerAbelWeight_nonneg hσ.le n)]
  exact mul_le_mul_of_nonneg_right (hC n) (deningerAbelWeight_nonneg hσ.le n)

/-- **The limit candidate can be subtracted inside the Abel average**, because the weight sums to
one. -/
theorem deningerAbelAverage_sub {b : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |b n| ≤ C) {σ : ℝ}
    (hσ : 0 < σ) (S : ℝ) :
    (∑' n : ℕ, b n * deningerAbelWeight σ n) - S
      = ∑' n : ℕ, (b n - S) * deningerAbelWeight σ n := by
  have hone := deningerAbelWeight_hasSum_one hσ
  have hb := deningerAbelAverage_summable hC hσ
  have hS : Summable fun n : ℕ => S * deningerAbelWeight σ n := hone.summable.mul_left S
  have hsplit : (∑' n : ℕ, (b n - S) * deningerAbelWeight σ n)
      = (∑' n : ℕ, b n * deningerAbelWeight σ n)
        - ∑' n : ℕ, S * deningerAbelWeight σ n := by
    rw [← Summable.tsum_sub hb hS]
    refine tsum_congr fun n => ?_
    ring
  rw [hsplit, Summable.tsum_mul_left _ hone.summable, hone.tsum_eq, mul_one]

/-- The Abel average of a bounded sequence is within the sequence's own bounds of the tail
threshold: the head contributes at most its own weight. -/
theorem deningerAbelAverage_tail_bound {b : ℕ → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (S : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ}
    (htail : ∀ n, N ≤ n → |b n - S| ≤ ε) :
    |∑' n : ℕ, (b (n + N) - S) * deningerAbelWeight σ (n + N)| ≤ ε := by
  have hone := deningerAbelWeight_hasSum_one hσ
  have hwshift : Summable fun n : ℕ => deningerAbelWeight σ (n + N) :=
    (hone.summable.comp_injective (add_left_injective N))
  have hbshift : Summable fun n : ℕ => (b (n + N) - S) * deningerAbelWeight σ (n + N) := by
    refine Summable.of_norm_bounded (g := fun n => ε * deningerAbelWeight σ (n + N))
      (hwshift.mul_left ε) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (deningerAbelWeight_nonneg hσ.le _)]
    exact mul_le_mul_of_nonneg_right (htail (n + N) (Nat.le_add_left N n))
      (deningerAbelWeight_nonneg hσ.le _)
  have hbound : ∀ n : ℕ, ‖(b (n + N) - S) * deningerAbelWeight σ (n + N)‖
      ≤ ε * deningerAbelWeight σ (n + N) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (deningerAbelWeight_nonneg hσ.le _)]
    exact mul_le_mul_of_nonneg_right (htail (n + N) (Nat.le_add_left N n))
      (deningerAbelWeight_nonneg hσ.le _)
  have hnormsummable : Summable fun n : ℕ =>
      ‖(b (n + N) - S) * deningerAbelWeight σ (n + N)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound (hwshift.mul_left ε)
  refine le_trans (norm_tsum_le_tsum_norm hnormsummable) ?_
  refine le_trans (Summable.tsum_le_tsum hbound hnormsummable (hwshift.mul_left ε)) ?_
  rw [Summable.tsum_mul_left _ hwshift]
  have hle : (∑' n : ℕ, deningerAbelWeight σ (n + N)) ≤ 1 := by
    have hnn : ∀ n : ℕ, 0 ≤ deningerAbelWeight σ n := deningerAbelWeight_nonneg hσ.le
    have := hone.tsum_eq
    refine le_trans (Summable.tsum_le_tsum_of_inj (fun n => n + N)
      (add_left_injective N) (fun m _ => hnn m) (fun n => le_of_eq rfl) hwshift
      hone.summable) (le_of_eq this)
  calc ε * (∑' n : ℕ, deningerAbelWeight σ (n + N)) ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left hle hε
    _ = ε := mul_one ε

end

end RHTower
