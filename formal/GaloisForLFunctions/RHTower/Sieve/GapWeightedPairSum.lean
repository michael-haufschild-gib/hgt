import GaloisForLFunctions.RHTower.Sieve.GapGroupedPairSum

/-!
# The weighted off-diagonal total

Bounding `|b(m₁)|·|b(m₂)|` by `(|b(m₁)|² + |b(m₂)|²)/2` and swapping the order of summation in the
second half turns the weighted off-diagonal total into the coefficient energy times the
one-dimensional gap sum.
-/

namespace RHTower.Sieve

open Finset

/-- Erasing a point is filtering it out. -/
theorem sum_erase_eq_sum_ite_finset (S : Finset ℕ) (f : ℕ → ℝ) (m : ℕ) :
    (∑ n ∈ S.erase m, f n) = ∑ n ∈ S, if n = m then 0 else f n := by
  classical
  rw [← Finset.filter_ne' S m, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n = m <;> simp [h]

/-- **The off-diagonal double sum over a finset is symmetric in its order.** -/
theorem sum_erase_swap_finset (S : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    (∑ m ∈ S, ∑ n ∈ S.erase m, g m n) = ∑ n ∈ S, ∑ m ∈ S.erase n, g m n := by
  classical
  have h1 : ∀ m ∈ S, (∑ n ∈ S.erase m, g m n) = ∑ n ∈ S, if n = m then 0 else g m n :=
    fun m _ => sum_erase_eq_sum_ite_finset S (g m) m
  have h2 : ∀ n ∈ S, (∑ m ∈ S.erase n, g m n) = ∑ m ∈ S, if m = n then 0 else g m n :=
    fun n _ => sum_erase_eq_sum_ite_finset S (fun m => g m n) n
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  by_cases h : m = n
  · simp [h]
  · simp [h, Ne.symm h]

/-- **The weighted off-diagonal total.** -/
theorem sum_offdiag_weighted_le (S : Finset ℕ) (H : ℕ) (b : ℕ → ℝ) (G : ℕ → ℝ)
    (hG : ∀ h, 0 ≤ G h)
    (hmap : ∀ m₁ ∈ S, ∀ m₂ ∈ S.erase m₁, Nat.dist m₁ m₂ ∈ Finset.Icc 1 H) :
    (∑ m₁ ∈ S, ∑ m₂ ∈ S.erase m₁, |b m₁| * |b m₂| * G (Nat.dist m₁ m₂))
      ≤ (∑ m ∈ S, |b m| ^ (2 : ℕ)) * (2 * ∑ h ∈ Finset.Icc 1 H, G h) := by
  classical
  set T : ℝ := ∑ h ∈ Finset.Icc 1 H, G h with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun h _ => hG h
  have hsplit : ∀ m₁ ∈ S, ∀ m₂ ∈ S.erase m₁,
      |b m₁| * |b m₂| * G (Nat.dist m₁ m₂)
        ≤ (|b m₁| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2 + (|b m₂| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2 := by
    intro m₁ _ m₂ _
    nlinarith [sq_nonneg (|b m₁| - |b m₂|), hG (Nat.dist m₁ m₂)]
  refine le_trans (Finset.sum_le_sum fun m₁ hm₁ =>
    Finset.sum_le_sum fun m₂ hm₂ => hsplit m₁ hm₁ m₂ hm₂) ?_
  have hdist : ∀ m₁ ∈ S,
      (∑ m₂ ∈ S.erase m₁, ((|b m₁| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2
          + (|b m₂| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2))
      = (∑ m₂ ∈ S.erase m₁, (|b m₁| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2)
        + ∑ m₂ ∈ S.erase m₁, (|b m₂| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2 :=
    fun m₁ _ => Finset.sum_add_distrib
  rw [Finset.sum_congr rfl hdist, Finset.sum_add_distrib]
  have hA : (∑ m₁ ∈ S, ∑ m₂ ∈ S.erase m₁, (|b m₁| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2)
      ≤ (∑ m ∈ S, |b m| ^ (2 : ℕ)) * T := by
    have hrow : ∀ m₁ ∈ S,
        (∑ m₂ ∈ S.erase m₁, (|b m₁| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2) ≤ |b m₁| ^ (2 : ℕ) * T := by
      intro m₁ hm₁
      have hgap := sum_row_gap_le S H G hG (fun m₂ hm₂ => hmap m₁ hm₁ m₂ hm₂)
      have hid : (∑ m₂ ∈ S.erase m₁, (|b m₁| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2)
          = |b m₁| ^ (2 : ℕ) / 2 * ∑ m₂ ∈ S.erase m₁, G (Nat.dist m₁ m₂) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m₂ _ => by ring
      rw [hid, ← hT] at *
      nlinarith [hgap, sq_nonneg (|b m₁|)]
    refine le_trans (Finset.sum_le_sum hrow) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  have hB : (∑ m₁ ∈ S, ∑ m₂ ∈ S.erase m₁, (|b m₂| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2)
      ≤ (∑ m ∈ S, |b m| ^ (2 : ℕ)) * T := by
    rw [sum_erase_swap_finset S (fun m₁ m₂ => (|b m₂| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2)]
    have hrow : ∀ m₂ ∈ S,
        (∑ m₁ ∈ S.erase m₂, (|b m₂| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2) ≤ |b m₂| ^ (2 : ℕ) * T := by
      intro m₂ hm₂
      have hgap := sum_row_gap_le S H G hG (fun m₁ hm₁ => by
        have h := hmap m₂ hm₂ m₁ hm₁
        rwa [Nat.dist_comm] at h ⊢)
      have hid : (∑ m₁ ∈ S.erase m₂, (|b m₂| ^ (2 : ℕ) * G (Nat.dist m₁ m₂)) / 2)
          = |b m₂| ^ (2 : ℕ) / 2 * ∑ m₁ ∈ S.erase m₂, G (Nat.dist m₂ m₁) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [Nat.dist_comm m₂ m₁]
        ring
      rw [hid, ← hT] at *
      nlinarith [hgap, sq_nonneg (|b m₂|)]
    refine le_trans (Finset.sum_le_sum hrow) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  have hfin : (∑ m ∈ S, |b m| ^ (2 : ℕ)) * T + (∑ m ∈ S, |b m| ^ (2 : ℕ)) * T
      = (∑ m ∈ S, |b m| ^ (2 : ℕ)) * (2 * T) := by ring
  linarith [hA, hB, hfin]

end RHTower.Sieve
