import Mathlib

/-!
# Truncating an Euler product by the number of factors

A sieve bounding sum is a sum over the divisors of a squarefree modulus subject to a size
restriction.  Restricting instead to divisors with **few prime factors** makes the size restriction
automatic, and costs almost nothing: the discarded subsets are bounded by Rankin's trick applied to
the *cardinality*, which turns the tail into `e^{-k}∏(1 + e·a_p) ≤ exp(e∑a_p − k)`.

So once `k` exceeds `e∑a_p`, half the Euler product survives — an elementary substitute for the
fundamental lemma of sieve theory in the only form the short-interval argument needs.
-/

namespace RHTower.Sieve

open Finset

/-- The Euler product as a sum over subsets. -/
theorem sum_powerset_prod_eq {s : Finset ℕ} (a : ℕ → ℝ) :
    ∑ t ∈ s.powerset, ∏ p ∈ t, a p = ∏ p ∈ s, (a p + 1) := by
  classical
  rw [Finset.prod_add]
  refine (Finset.sum_congr rfl fun t _ => ?_).symm
  simp

/-- **The subsets with many elements contribute little.**  Rankin's trick in the cardinality
variable. -/
theorem sum_powerset_card_gt_le {s : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ p ∈ s, 0 ≤ a p) (k : ℕ) :
    ∑ t ∈ s.powerset.filter (fun t => ¬ t.card ≤ k), ∏ p ∈ t, a p
      ≤ Real.exp (Real.exp 1 * (∑ p ∈ s, a p) - k) := by
  classical
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hstep : ∀ t ∈ s.powerset.filter (fun t => ¬ t.card ≤ k),
      (∏ p ∈ t, a p) ≤ (∏ p ∈ t, Real.exp 1 * a p) / Real.exp 1 ^ k := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    have hcard : k < t.card := by omega
    have hnn : (0 : ℝ) ≤ ∏ p ∈ t, a p :=
      Finset.prod_nonneg fun p hp => ha p (ht.1 hp)
    have hexp : (∏ p ∈ t, Real.exp 1 * a p) = Real.exp 1 ^ t.card * ∏ p ∈ t, a p := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    rw [hexp, le_div_iff₀ (by positivity)]
    have hpow : Real.exp 1 ^ k ≤ Real.exp 1 ^ t.card :=
      pow_le_pow_right₀ (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by omega)
    nlinarith [hnn, hpow, pow_pos he k]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_div]
  have hext : (∑ t ∈ s.powerset.filter (fun t => ¬ t.card ≤ k), ∏ p ∈ t, Real.exp 1 * a p)
      ≤ ∑ t ∈ s.powerset, ∏ p ∈ t, Real.exp 1 * a p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun t ht _ => ?_
    rw [Finset.mem_powerset] at ht
    exact Finset.prod_nonneg fun p hp => by
      have := ha p (ht hp)
      positivity
  refine le_trans (by
    exact div_le_div_of_nonneg_right hext (by positivity)) ?_
  rw [sum_powerset_prod_eq]
  have hbound : (∏ p ∈ s, (Real.exp 1 * a p + 1)) ≤ Real.exp (Real.exp 1 * ∑ p ∈ s, a p) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => by
      have := ha p hp
      positivity) fun p hp => ?_
    have := Real.add_one_le_exp (Real.exp 1 * a p)
    linarith
  rw [Real.exp_sub, ← Real.exp_one_pow k]
  exact div_le_div_of_nonneg_right hbound (by positivity)

/-- **Half the Euler product survives the truncation.** -/
theorem sum_powerset_card_le_ge {s : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ p ∈ s, 0 ≤ a p) (k : ℕ)
    (hk : Real.exp 1 * (∑ p ∈ s, a p) + Real.log 2 ≤ (k : ℝ)) :
    (1 / 2) * ∏ p ∈ s, (a p + 1)
      ≤ ∑ t ∈ s.powerset.filter (fun t => t.card ≤ k), ∏ p ∈ t, a p := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s.powerset
    (fun t => t.card ≤ k) (fun t => ∏ p ∈ t, a p)
  have htail := sum_powerset_card_gt_le ha k
  have hle : Real.exp (Real.exp 1 * (∑ p ∈ s, a p) - k) ≤ 1 / 2 := by
    have harg : Real.exp 1 * (∑ p ∈ s, a p) - (k : ℝ) ≤ -Real.log 2 := by linarith
    refine (Real.exp_le_exp.2 harg).trans (le_of_eq ?_)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  have hprod1 : (1 : ℝ) ≤ ∏ p ∈ s, (a p + 1) := by
    refine one_le_prod fun p hp => ?_
    have := ha p hp
    linarith
  rw [sum_powerset_prod_eq] at hsplit
  linarith [hsplit, htail, hle, hprod1]

end RHTower.Sieve
