import GaloisForLFunctions.RHTower.Sieve.KubalalikaBlockScale

/-!
# Dyadic assembly of an interval sum

An interval `[a, b)` with `1 ≤ a ≤ b` is the disjoint union of the `⌊log₂ b⌋ + 1` truncated dyadic
blocks `[min b (a 2^j), min b (a 2^{j+1}))`, each of which has its right endpoint at most twice its
left endpoint.  A bound valid on every such block therefore costs only the block count.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **Partition of an interval along a monotone sequence of endpoints.** -/
theorem sum_Ico_monotone_partition {M : Type*} [AddCommMonoid M] (f : ℕ → M) (c : ℕ → ℕ)
    (hc : Monotone c) (R : ℕ) :
    ∑ n ∈ Finset.Ico (c 0) (c R), f n
      = ∑ j ∈ Finset.range R, ∑ n ∈ Finset.Ico (c j) (c (j + 1)), f n := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ← ih,
        Finset.sum_Ico_consecutive f (hc (Nat.zero_le R)) (hc (Nat.le_succ R))]

/-- **A uniform block bound costs only the dyadic block count.** -/
theorem norm_sum_Ico_le_of_blocks {E : Type*} [NormedAddCommGroup E] {a b : ℕ} (f : ℕ → E)
    (G : ℝ) (hab : a ≤ b) (ha : 1 ≤ a) (hG : 0 ≤ G)
    (hblock : ∀ A B : ℕ, 1 ≤ A → A ≤ B → B ≤ 2 * A → a ≤ A → B ≤ b →
      ‖∑ n ∈ Finset.Ico A B, f n‖ ≤ G) :
    ‖∑ n ∈ Finset.Ico a b, f n‖ ≤ 2 * (1 + Real.log b) * G := by
  have hb : 1 ≤ b := le_trans ha hab
  set R : ℕ := Nat.log 2 b + 1 with hRdef
  set c : ℕ → ℕ := fun j => min b (a * 2 ^ j) with hcdef
  have hmono : Monotone c := by
    intro i j hij
    exact min_le_min le_rfl (Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by norm_num) hij))
  have hc0 : c 0 = a := by
    rw [hcdef]
    simp only [pow_zero, mul_one]
    exact min_eq_right hab
  have hcR : c R = b := by
    have hlt : b < 2 ^ R := Nat.lt_pow_succ_log_self (by norm_num) b
    have hle : b ≤ a * 2 ^ R := le_trans hlt.le (Nat.le_mul_of_pos_left _ (by omega))
    rw [hcdef]
    exact min_eq_left hle
  have hdecomp : ‖∑ n ∈ Finset.Ico a b, f n‖
      ≤ ∑ j ∈ Finset.range R, ‖∑ n ∈ Finset.Ico (c j) (c (j + 1)), f n‖ := by
    rw [← hc0, ← hcR, sum_Ico_monotone_partition f c hmono R]
    exact norm_sum_le _ _
  have hterm : ∀ j ∈ Finset.range R, ‖∑ n ∈ Finset.Ico (c j) (c (j + 1)), f n‖ ≤ G := by
    intro j _
    have haA : a ≤ c j := by
      rw [← hc0]
      exact hmono (Nat.zero_le j)
    have hA1 : 1 ≤ c j := le_trans ha haA
    have hAB : c j ≤ c (j + 1) := hmono (Nat.le_succ j)
    have hBb : c (j + 1) ≤ b := min_le_left _ _
    have hB2 : c (j + 1) ≤ 2 * c j := by
      have hpow : a * 2 ^ (j + 1) = 2 * (a * 2 ^ j) := by ring
      rcases le_total b (a * 2 ^ j) with h | h
      · have h1 : c j = b := by rw [hcdef]; exact min_eq_left h
        have h2 : c (j + 1) = b := by
          rw [hcdef]
          exact min_eq_left (le_trans h (by rw [hpow]; omega))
        rw [h1, h2]
        omega
      · have h1 : c j = a * 2 ^ j := by rw [hcdef]; exact min_eq_right h
        rw [h1]
        calc c (j + 1) ≤ a * 2 ^ (j + 1) := by rw [hcdef]; exact min_le_right _ _
          _ = 2 * (a * 2 ^ j) := hpow
    exact hblock (c j) (c (j + 1)) hA1 hAB hB2 haA hBb
  have hsum : ∑ j ∈ Finset.range R, ‖∑ n ∈ Finset.Ico (c j) (c (j + 1)), f n‖
      ≤ (R : ℝ) * G := by
    calc ∑ j ∈ Finset.range R, ‖∑ n ∈ Finset.Ico (c j) (c (j + 1)), f n‖
        ≤ ∑ _j ∈ Finset.range R, G := Finset.sum_le_sum hterm
      _ = (R : ℝ) * G := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hRle : (R : ℝ) ≤ 2 * (1 + Real.log b) := by
    have h := natLogTwo_succ_le_two_mul_one_add_log hb
    rw [hRdef]
    push_cast
    linarith
  calc ‖∑ n ∈ Finset.Ico a b, f n‖
      ≤ ∑ j ∈ Finset.range R, ‖∑ n ∈ Finset.Ico (c j) (c (j + 1)), f n‖ := hdecomp
    _ ≤ (R : ℝ) * G := hsum
    _ ≤ 2 * (1 + Real.log b) * G := mul_le_mul_of_nonneg_right hRle hG

end

end RHTower.Sieve
