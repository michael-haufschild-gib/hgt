import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Greedy two-sided rounding of a signed target

Let `P` be a set of sites in `ℕ` with weights `w`, and let `m : ℕ → ℝ` be a signed target.  The
greedy rounding walks through `k = 1, 2, …` with the running discrepancy
`δ(k) = Σ_{0<j≤k} (m(j) − ε(j) w(j))` and chooses `ε(k) = +1` at a site where
`δ(k−1) + m(k) ≥ w(k)`, `ε(k) = −1` at a site where `δ(k−1) + m(k) ≤ −w(k)`, and `ε(k) = 0`
otherwise.

* **Thinness** (`abs_disc_add_sum_le`).  `|δ(n)| + Σ_{k≤n} |ε(k)| w(k) ≤ Σ_{k≤n} |m(k)|`: a rounded
  site lowers `|δ|` by its weight.
* **Discrepancy** (`abs_disc_le_of_window`).  Let `τ` be monotone with `w ≤ τ`.  If on every
  interval `(a, n]` the drift `Σ |m(k)|` is at most `B(n)` plus the mass of the sites of the
  interval, then `|δ(n)| ≤ τ(n) + B(n)`.  After the last index with `δ ≤ τ` every site is rounded
  up, so the excess is the drift minus the site mass.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.GreedyRounding

variable (P : ℕ → Prop) (w m : ℕ → ℝ)

open Classical in
/-- The sign chosen at `k` when the discrepancy before rounding is `d`. -/
def choice (k : ℕ) (d : ℝ) : ℤ :=
  if P k ∧ w k ≤ d then 1 else if P k ∧ d ≤ -w k then -1 else 0

/-- The running discrepancy `δ(n) = Σ_{0<k≤n} (m(k) − ε(k) w(k))` of the greedy rounding. -/
def disc : ℕ → ℝ
  | 0 => 0
  | k + 1 => disc k + m (k + 1) - choice P w (k + 1) (disc k + m (k + 1)) * w (k + 1)

/-- The sign `ε(k) ∈ {−1, 0, 1}` of the greedy rounding; `ε(0) = 0`. -/
def sgn : ℕ → ℤ
  | 0 => 0
  | k + 1 => choice P w (k + 1) (disc P w m k + m (k + 1))

@[simp] theorem disc_zero : disc P w m 0 = 0 := rfl

@[simp] theorem sgn_zero : sgn P w m 0 = 0 := rfl

theorem sgn_succ (k : ℕ) :
    sgn P w m (k + 1) = choice P w (k + 1) (disc P w m k + m (k + 1)) := rfl

theorem disc_succ (k : ℕ) :
    disc P w m (k + 1) = disc P w m k + m (k + 1) - sgn P w m (k + 1) * w (k + 1) := rfl

/-- The three branches of the choice. -/
theorem choice_cases (k : ℕ) (d : ℝ) :
    (choice P w k d = 1 ∧ P k ∧ w k ≤ d) ∨ (choice P w k d = -1 ∧ P k ∧ d ≤ -w k) ∨
      (choice P w k d = 0 ∧ (P k → d < w k ∧ -w k < d)) := by
  classical
  unfold choice
  by_cases h1 : P k ∧ w k ≤ d
  · exact Or.inl ⟨if_pos h1, h1⟩
  · by_cases h2 : P k ∧ d ≤ -w k
    · exact Or.inr (Or.inl ⟨by rw [if_neg h1, if_pos h2], h2⟩)
    · refine Or.inr (Or.inr ⟨by rw [if_neg h1, if_neg h2], fun hP => ⟨?_, ?_⟩⟩)
      · exact lt_of_not_ge fun h => h1 ⟨hP, h⟩
      · exact lt_of_not_ge fun h => h2 ⟨hP, h⟩

theorem sgn_cases (k : ℕ) : sgn P w m k = 1 ∨ sgn P w m k = -1 ∨ sgn P w m k = 0 := by
  cases k with
  | zero => exact Or.inr (Or.inr rfl)
  | succ j =>
    rw [sgn_succ]
    rcases choice_cases P w (j + 1) (disc P w m j + m (j + 1)) with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr h.1)

/-- Only sites are rounded. -/
theorem sgn_eq_zero_of_not {k : ℕ} (hk : ¬ P k) : sgn P w m k = 0 := by
  cases k with
  | zero => rfl
  | succ j =>
    rw [sgn_succ]
    rcases choice_cases P w (j + 1) (disc P w m j + m (j + 1)) with h | h | h
    · exact absurd h.2.1 hk
    · exact absurd h.2.1 hk
    · exact h.1

theorem abs_sgn_le_one (k : ℕ) : |(sgn P w m k : ℝ)| ≤ 1 := by
  rcases sgn_cases P w m k with h | h | h <;> rw [h] <;> simp

/-- The discrepancy on an interval. -/
theorem disc_eq_add_sum {a n : ℕ} (han : a ≤ n) :
    disc P w m n = disc P w m a + ∑ k ∈ Ioc a n, (m k - sgn P w m k * w k) := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ n han ih => rw [Finset.sum_Ioc_succ_top han, ← add_assoc, ← ih, disc_succ]; ring

theorem disc_eq_sum (n : ℕ) :
    disc P w m n = ∑ k ∈ Ioc 0 n, (m k - sgn P w m k * w k) := by
  simpa using disc_eq_add_sum P w m (Nat.zero_le n)

/-- One step of the rounding: the discrepancy and the rounded weight together grow by at most
`|m|`. -/
theorem abs_disc_succ_add_le (n : ℕ) :
    |disc P w m (n + 1)| + |(sgn P w m (n + 1) : ℝ)| * w (n + 1) ≤
      |disc P w m n| + |m (n + 1)| := by
  have hd := abs_add_le (disc P w m n) (m (n + 1))
  rw [disc_succ, sgn_succ]
  rcases choice_cases P w (n + 1) (disc P w m n + m (n + 1)) with ⟨hc, -, h⟩ | ⟨hc, -, h⟩ | ⟨hc, -⟩
  · rw [hc]
    simp only [Int.cast_one, one_mul, abs_one]
    rw [abs_of_nonneg (by linarith)]
    linarith [le_abs_self (disc P w m n + m (n + 1))]
  · rw [hc]
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, abs_neg, abs_one, sub_neg_eq_add]
    rw [abs_of_nonpos (by linarith)]
    linarith [neg_le_abs (disc P w m n + m (n + 1))]
  · rw [hc]
    simp only [Int.cast_zero, zero_mul, abs_zero, sub_zero, add_zero]
    exact hd

/-- **Thinness.**  The discrepancy and the rounded weight are paid by the target. -/
theorem abs_disc_add_sum_le (n : ℕ) :
    |disc P w m n| + ∑ k ∈ Ioc 0 n, |(sgn P w m k : ℝ)| * w k ≤ ∑ k ∈ Ioc 0 n, |m k| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), Finset.sum_Ioc_succ_top (Nat.zero_le n)]
    linarith [abs_disc_succ_add_le P w m n]

/-- At a site that is not rounded up the discrepancy is at most the weight. -/
theorem disc_le_of_sgn_ne_one {k : ℕ} (hw : 0 ≤ w (k + 1)) (hP : P (k + 1))
    (h : sgn P w m (k + 1) ≠ 1) : disc P w m (k + 1) ≤ w (k + 1) := by
  rw [disc_succ]
  rw [sgn_succ] at h ⊢
  rcases choice_cases P w (k + 1) (disc P w m k + m (k + 1)) with ⟨hc, -⟩ | ⟨hc, -, hd⟩ | ⟨hc, hd⟩
  · exact absurd hc h
  · rw [hc]; push_cast; linarith
  · rw [hc]; push_cast; linarith [(hd hP).1]

/-- At a site that is not rounded down the discrepancy is at least minus the weight. -/
theorem neg_disc_le_of_sgn_ne_neg_one {k : ℕ} (hw : 0 ≤ w (k + 1)) (hP : P (k + 1))
    (h : sgn P w m (k + 1) ≠ -1) : -disc P w m (k + 1) ≤ w (k + 1) := by
  rw [disc_succ]
  rw [sgn_succ] at h ⊢
  rcases choice_cases P w (k + 1) (disc P w m k + m (k + 1)) with ⟨hc, -, hd⟩ | ⟨hc, -⟩ | ⟨hc, hd⟩
  · rw [hc]; push_cast; linarith
  · exact absurd hc h
  · rw [hc]; push_cast; linarith [(hd hP).2]

/-- The last index up to `n` at which a sequence is below a threshold. -/
theorem exists_last_le {δ τ : ℕ → ℝ} (h0 : δ 0 ≤ τ 0) (n : ℕ) :
    ∃ a ≤ n, δ a ≤ τ a ∧ ∀ k, a < k → k ≤ n → τ k < δ k := by
  classical
  refine ⟨Nat.findGreatest (fun k => δ k ≤ τ k) n, Nat.findGreatest_le n, ?_, fun k hak hkn => ?_⟩
  · exact Nat.findGreatest_spec (P := fun k => δ k ≤ τ k) (Nat.zero_le n) h0
  · exact lt_of_not_ge (Nat.findGreatest_is_greatest hak hkn)

variable {P w m}

/-- **Upper discrepancy.**  If the drift on every interval is paid by its site mass up to `B`,
the discrepancy is at most `τ + B`. -/
theorem disc_le_of_window [DecidablePred P] {τ B : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (hτ : Monotone τ) (hτ0 : 0 ≤ τ 0)
    (hwτ : ∀ k, w k ≤ τ k)
    (hwin : ∀ a n : ℕ, a ≤ n →
      ∑ k ∈ Ioc a n, |m k| ≤ B n + ∑ k ∈ Ioc a n, if P k then w k else 0)
    (n : ℕ) : disc P w m n ≤ τ n + B n := by
  obtain ⟨a, han, hlow, hhigh⟩ := exists_last_le (δ := disc P w m) (τ := τ) (by simpa using hτ0) n
  -- above the last low index every site is rounded up
  have hsgn : ∀ k ∈ Ioc a n, (sgn P w m k : ℝ) * w k = if P k then w k else 0 := by
    intro k hk
    obtain ⟨hak, hkn⟩ := Finset.mem_Ioc.mp hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    by_cases hP : P (j + 1)
    · have h1 : sgn P w m (j + 1) = 1 := by
        by_contra hne
        have := disc_le_of_sgn_ne_one P w m (hw _) hP hne
        linarith [hhigh (j + 1) hak hkn, hwτ (j + 1)]
      rw [if_pos hP, h1]; simp
    · rw [if_neg hP, sgn_eq_zero_of_not P w m hP]; simp
  have hform := disc_eq_add_sum P w m han
  rw [Finset.sum_sub_distrib, Finset.sum_congr rfl hsgn] at hform
  have hm : ∑ k ∈ Ioc a n, m k ≤ ∑ k ∈ Ioc a n, |m k| :=
    Finset.sum_le_sum fun k _ => le_abs_self _
  linarith [hwin a n han, hτ han]

/-- **Lower discrepancy.** -/
theorem neg_disc_le_of_window [DecidablePred P] {τ B : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (hτ : Monotone τ)
    (hτ0 : 0 ≤ τ 0) (hwτ : ∀ k, w k ≤ τ k)
    (hwin : ∀ a n : ℕ, a ≤ n →
      ∑ k ∈ Ioc a n, |m k| ≤ B n + ∑ k ∈ Ioc a n, if P k then w k else 0)
    (n : ℕ) : -disc P w m n ≤ τ n + B n := by
  obtain ⟨a, han, hlow, hhigh⟩ :=
    exists_last_le (δ := fun k => -disc P w m k) (τ := τ) (by simpa using hτ0) n
  -- above the last high index every site is rounded down
  have hsgn : ∀ k ∈ Ioc a n, (sgn P w m k : ℝ) * w k = -(if P k then w k else 0) := by
    intro k hk
    obtain ⟨hak, hkn⟩ := Finset.mem_Ioc.mp hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    by_cases hP : P (j + 1)
    · have h1 : sgn P w m (j + 1) = -1 := by
        by_contra hne
        have := neg_disc_le_of_sgn_ne_neg_one P w m (hw _) hP hne
        linarith [hhigh (j + 1) hak hkn, hwτ (j + 1)]
      rw [if_pos hP, h1]; simp
    · rw [if_neg hP, sgn_eq_zero_of_not P w m hP]; simp
  have hform := disc_eq_add_sum P w m han
  rw [Finset.sum_sub_distrib, Finset.sum_congr rfl hsgn, Finset.sum_neg_distrib] at hform
  have hm : -∑ k ∈ Ioc a n, |m k| ≤ ∑ k ∈ Ioc a n, m k := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun k _ => neg_abs_le _
  have hlow' : -disc P w m a ≤ τ a := hlow
  linarith [hwin a n han, hτ han]

/-- **Discrepancy of the greedy rounding.** -/
theorem abs_disc_le_of_window [DecidablePred P] {τ B : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (hτ : Monotone τ)
    (hτ0 : 0 ≤ τ 0) (hwτ : ∀ k, w k ≤ τ k)
    (hwin : ∀ a n : ℕ, a ≤ n →
      ∑ k ∈ Ioc a n, |m k| ≤ B n + ∑ k ∈ Ioc a n, if P k then w k else 0)
    (n : ℕ) : |disc P w m n| ≤ τ n + B n :=
  abs_le.mpr ⟨by linarith [neg_disc_le_of_window hw hτ hτ0 hwτ hwin n],
    disc_le_of_window hw hτ hτ0 hwτ hwin n⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.GreedyRounding
