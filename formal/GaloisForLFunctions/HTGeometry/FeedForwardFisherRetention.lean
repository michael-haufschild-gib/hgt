import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Feed-forward Fisher-information retention

Theorem S4 and equations (19), (24), and (28) of Bai--Li--Kou,
arXiv:2609.04996. Nonempty intervals are indexed by `Fin (n+1)`.
The shared-probe optimum includes an explicit unit-energy attaining vector and
an upper bound for every competitor. All parameters are unrestricted; the
directional-gain regime is parametrized by the amplitude `1+a²`.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Preparation energy of a nonempty feed-forward interval, for arbitrary real hopping amplitude. -/
def feedForwardBuildup (r : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), (r ^ (2 : ℕ)) ^ i.val

theorem feedForwardBuildup_one_le (r : ℝ) (n : ℕ) : 1 ≤ feedForwardBuildup r n := by
  have h := Finset.single_le_sum
    (f := fun i : Fin (n + 1) => (r ^ (2 : ℕ)) ^ i.val)
    (fun i _ => pow_nonneg (sq_nonneg r) _) (Finset.mem_univ (0 : Fin (n + 1)))
  simpa [feedForwardBuildup] using h

theorem feedForwardBuildup_pos (r : ℝ) (n : ℕ) : 0 < feedForwardBuildup r n :=
  lt_of_lt_of_le zero_lt_one (feedForwardBuildup_one_le r n)

/-- Site-local Fisher retention, including the zero-hopping limit. -/
def feedForwardRetention (r : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (r ^ (2 : ℕ)) ^ i.val / feedForwardBuildup r n

/-- Theorem S4, equation (S84): each port interval has exactly one unit of retention. -/
theorem sum_feedForwardRetention (r : ℝ) (n : ℕ) :
    ∑ i, feedForwardRetention r n i = 1 := by
  simp only [feedForwardRetention, ← Finset.sum_div]
  exact div_self (ne_of_gt (feedForwardBuildup_pos r n))

theorem feedForwardRetention_nonneg (r : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ feedForwardRetention r n i :=
  div_nonneg (pow_nonneg (sq_nonneg r) _) (feedForwardBuildup_pos r n).le

theorem feedForwardRetention_le_one (r : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    feedForwardRetention r n i ≤ 1 := by
  rw [feedForwardRetention, div_le_one (feedForwardBuildup_pos r n)]
  exact Finset.single_le_sum (fun j _ => pow_nonneg (sq_nonneg r) _)
    (Finset.mem_univ i)

/-- Source buildup times upstream coverage is exactly one, equation (19). -/
theorem feedForwardBuildup_mul_upstreamRetention (r : ℝ) (n : ℕ) :
    feedForwardBuildup r n * feedForwardRetention r n 0 = 1 := by
  simp [feedForwardRetention, ne_of_gt (feedForwardBuildup_pos r n)]

/-- The finite-geometric closed form without a singular division at unit hopping. -/
theorem feedForwardBuildup_geometric_identity (r : ℝ) (n : ℕ) :
    feedForwardBuildup r n * (r ^ (2 : ℕ) - 1) = (r ^ (2 : ℕ)) ^ (n + 1) - 1 := by
  simpa [feedForwardBuildup, Fin.sum_univ_eq_sum_range] using geom_sum_mul (r ^ (2 : ℕ)) (n + 1)

theorem feedForwardBuildup_succ (r : ℝ) (n : ℕ) :
    feedForwardBuildup r (n + 1) = feedForwardBuildup r n + (r ^ (2 : ℕ)) ^ (n + 1) := by
  simp only [feedForwardBuildup, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

/-- Unit hopping spreads coverage uniformly. -/
theorem feedForwardRetention_one (n : ℕ) (i : Fin (n + 1)) :
    feedForwardRetention 1 n i = 1 / (n + 1 : ℝ) := by
  simp [feedForwardRetention, feedForwardBuildup]

/-- The zero-hopping limit retains exactly the driven site. -/
theorem feedForwardRetention_zero (n : ℕ) (i : Fin (n + 1)) :
    feedForwardRetention 0 n i = if i.val = 0 then 1 else 0 := by
  have hS : feedForwardBuildup 0 n = 1 := by
    rw [feedForwardBuildup, Fin.sum_univ_succ]
    simp
  simp [feedForwardRetention, hS, zero_pow_eq]

/-- The budget is the number of ports even when interval lengths and couplings vary. -/
theorem sum_feedForwardRetention_intervals {m : ℕ}
    (r : Fin m → ℝ) (n : Fin m → ℕ) :
    ∑ j, ∑ i, feedForwardRetention (r j) (n j) i = (m : ℝ) := by
  simp [sum_feedForwardRetention]

/-- An interval always contains a task no better than the average coverage. -/
theorem exists_feedForwardRetention_le_average (r : ℝ) (n : ℕ) :
    ∃ i, feedForwardRetention r n i ≤ 1 / (n + 1 : ℝ) := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hs : (∑ i : Fin (n + 1), feedForwardRetention r n i) ≤
      ∑ _i : Fin (n + 1), 1 / (n + 1 : ℝ) := by
    rw [sum_feedForwardRetention]
    simp [hn]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨i, hi⟩

/-- At hopping amplitude `1+a²`, upstream is a weakest task. -/
theorem upstreamRetention_le_directedRetention (a : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    feedForwardRetention (1 + a ^ (2 : ℕ)) n 0 ≤ feedForwardRetention (1 + a ^ (2 : ℕ)) n i := by
  apply div_le_div_of_nonneg_right _ (feedForwardBuildup_pos _ _).le
  simp only [Fin.val_zero, pow_zero]
  exact one_le_pow₀ (by nlinarith [sq_nonneg a, sq_nonneg (a ^ (2 : ℕ))])

/-- Minimal interval preparation costs are summed by a probe shared across every task. -/
def feedForwardCommonCost {m : ℕ} (r : ℝ) (n : Fin (m + 1) → ℕ) : ℝ :=
  ∑ j, feedForwardBuildup r (n j)

theorem feedForwardCommonCost_pos {m : ℕ} (r : ℝ) (n : Fin (m + 1) → ℕ) :
    0 < feedForwardCommonCost r n :=
  Finset.sum_pos (fun j _ => feedForwardBuildup_pos r (n j)) Finset.univ_nonempty

/-- Explicit amplitudes attaining equal upstream intensities with total resource one. -/
def feedForwardBalancedProbe {m : ℕ} (r : ℝ) (n : Fin (m + 1) → ℕ)
    (j : Fin (m + 1)) : ℝ :=
  Real.sqrt (feedForwardBuildup r (n j) / feedForwardCommonCost r n)

theorem feedForwardBalancedProbe_sq {m : ℕ} (r : ℝ) (n : Fin (m + 1) → ℕ)
    (j : Fin (m + 1)) :
    feedForwardBalancedProbe r n j ^ (2 : ℕ) =
      feedForwardBuildup r (n j) / feedForwardCommonCost r n :=
  Real.sq_sqrt (div_nonneg (feedForwardBuildup_pos _ _).le
    (feedForwardCommonCost_pos _ _).le)

theorem sum_sq_feedForwardBalancedProbe {m : ℕ} (r : ℝ) (n : Fin (m + 1) → ℕ) :
    ∑ j, feedForwardBalancedProbe r n j ^ (2 : ℕ) = 1 := by
  simp only [feedForwardBalancedProbe_sq, ← Finset.sum_div]
  exact div_self (ne_of_gt (feedForwardCommonCost_pos r n))

theorem feedForwardBalancedProbe_upstream {m : ℕ} (r : ℝ)
    (n : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    feedForwardBalancedProbe r n j ^ (2 : ℕ) * feedForwardRetention r (n j) 0 =
      1 / feedForwardCommonCost r n := by
  rw [feedForwardBalancedProbe_sq, feedForwardRetention]
  simp only [Fin.val_zero, pow_zero]
  field_simp [ne_of_gt (feedForwardBuildup_pos r (n j)),
    ne_of_gt (feedForwardCommonCost_pos r n)]

/-- Every probe has an upstream task bounded by total energy divided by summed interval costs. -/
theorem exists_feedForwardProbe_bottleneck {m : ℕ} (r : ℝ)
    (n : Fin (m + 1) → ℕ) (a : Fin (m + 1) → ℝ) :
    ∃ j, a j ^ (2 : ℕ) * feedForwardRetention r (n j) 0 ≤
      (∑ k, a k ^ (2 : ℕ)) / feedForwardCommonCost r n := by
  have hc := feedForwardCommonCost_pos r n
  have hs : (∑ j, a j ^ (2 : ℕ)) ≤
      ∑ j, ((∑ k, a k ^ (2 : ℕ)) / feedForwardCommonCost r n) *
        feedForwardBuildup r (n j) := by
    rw [← Finset.mul_sum]
    change _ ≤ _ / feedForwardCommonCost r n * feedForwardCommonCost r n
    rw [div_mul_cancel₀ _ (ne_of_gt hc)]
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  refine ⟨j, ?_⟩
  simpa only [feedForwardRetention, Fin.val_zero, pow_zero, mul_one_div] using
    (div_le_iff₀ (feedForwardBuildup_pos r (n j))).mpr hj

/-- Equal intervals incur the paper's extra factor equal to the number of ports. -/
theorem feedForwardCommon_equal_intervals (r : ℝ) (m n : ℕ) :
    1 / feedForwardCommonCost r (fun _ : Fin (m + 1) => n) =
      feedForwardRetention r n 0 / (m + 1 : ℝ) := by
  simp only [feedForwardCommonCost, feedForwardRetention, Fin.val_zero, pow_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Coverages simultaneously achievable at every site by one unit-resource probe. -/
def feedForwardAchievableCoverage {m : ℕ} (r : ℝ) (n : Fin (m + 1) → ℕ) : Set ℝ :=
  {t | ∃ a : Fin (m + 1) → ℝ, (∑ j, a j ^ (2 : ℕ)) = 1 ∧
    ∀ j i, t ≤ a j ^ (2 : ℕ) * feedForwardRetention r (n j) i}

/-- Equation (28), with both optimality and an explicit attaining probe: the shared-probe
max–min value is the reciprocal of the sum of the segment preparation costs. -/
theorem feedForwardCommonProbe_isGreatest {m : ℕ} (a : ℝ)
    (n : Fin (m + 1) → ℕ) :
    IsGreatest (feedForwardAchievableCoverage (1 + a ^ (2 : ℕ)) n)
      (1 / feedForwardCommonCost (1 + a ^ (2 : ℕ)) n) := by
  constructor
  · refine ⟨feedForwardBalancedProbe (1 + a ^ (2 : ℕ)) n,
      sum_sq_feedForwardBalancedProbe _ _, ?_⟩
    intro j i
    rw [← feedForwardBalancedProbe_upstream (1 + a ^ (2 : ℕ)) n j]
    exact mul_le_mul_of_nonneg_left (upstreamRetention_le_directedRetention a (n j) i)
      (sq_nonneg _)
  · intro t ht
    obtain ⟨c, hc, hcover⟩ := ht
    obtain ⟨j, hj⟩ := exists_feedForwardProbe_bottleneck (1 + a ^ (2 : ℕ)) n c
    rw [hc] at hj
    exact (hcover j 0).trans hj

/-- Splitting an interval separates its preparation costs by the intervening gain. -/
theorem feedForwardBuildup_concat (r : ℝ) (n k : ℕ) :
    feedForwardBuildup r (n + k + 1) = feedForwardBuildup r n +
      (r ^ (2 : ℕ)) ^ (n + 1) * feedForwardBuildup r k := by
  unfold feedForwardBuildup
  have h := Fin.sum_univ_add (a := n + 1) (b := k + 1)
    (fun i => (r ^ (2 : ℕ)) ^ i.val)
  have he : n + k + 1 + 1 = (n + 1) + (k + 1) := by omega
  conv_lhs => rw [he]
  simpa only [Fin.val_castAdd, Fin.val_natAdd, pow_add, Finset.mul_sum] using h

/-- Every extra downstream site strictly reduces upstream coverage for directed gain. -/
theorem directed_upstreamRetention_strict_step (a : ℝ) (n : ℕ) :
    feedForwardRetention (1 + a ^ (2 : ℕ)) (n + 1) 0 <
      feedForwardRetention (1 + a ^ (2 : ℕ)) n 0 := by
  simp only [feedForwardRetention, Fin.val_zero, pow_zero, one_div]
  apply (inv_lt_inv₀ (feedForwardBuildup_pos _ _) (feedForwardBuildup_pos _ _)).mpr
  rw [feedForwardBuildup_succ]
  have hb : 0 < ((1 + a ^ (2 : ℕ)) ^ (2 : ℕ)) ^ (n + 1) := by positivity
  linarith

end GaloisForLFunctions.HTGeometry
