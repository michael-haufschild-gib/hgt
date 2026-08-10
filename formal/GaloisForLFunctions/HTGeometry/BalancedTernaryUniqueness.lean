import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Uniqueness of balanced ternary expansions

A signed sum of powers of three with coefficients in `{-1, 0, 1}` vanishes only when every
coefficient vanishes: the tail `∑_{j<n} 3^j` is strictly smaller than the leading power `3^n`,
so no leading coefficient can be cancelled from below.

The consequence used in spectral constructions is `sum_pow_three_sign_injOn`: the `2^n` values
`∑_j 3^j εⱼ` with `εⱼ = ±1` are pairwise distinct.  That is what makes the `X`-basis spectrum of
`∑_j 3^j X_j` simple, and hence what makes the Vandermonde cyclicity determinant of that
Hamiltonian nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

namespace BalancedTernary

open Finset

/-- Twice the truncated geometric sum of powers of three is one less than the next power. -/
theorem two_mul_geom_sum_add_one (n : ℕ) :
    2 * ∑ j ∈ range n, (3 : ℤ) ^ j + 1 = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linarith [ih]

/-- The tail of a balanced ternary sum is dominated by the next power of three. -/
theorem abs_sum_lt_pow (n : ℕ) (c : ℕ → ℤ) (hc : ∀ j, |c j| ≤ 1) :
    |∑ j ∈ range n, (3 : ℤ) ^ j * c j| < 3 ^ n := by
  have hle : |∑ j ∈ range n, (3 : ℤ) ^ j * c j| ≤ ∑ j ∈ range n, (3 : ℤ) ^ j := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 3)]
    calc (3 : ℤ) ^ j * |c j| ≤ 3 ^ j * 1 :=
          mul_le_mul_of_nonneg_left (hc j) (by positivity)
      _ = 3 ^ j := mul_one _
  have hgeom := two_mul_geom_sum_add_one n
  have hpos : (0 : ℤ) < 3 ^ n := by positivity
  linarith
/-- **Uniqueness of balanced ternary expansions.** -/
theorem eq_zero_of_sum_eq_zero (n : ℕ) (c : ℕ → ℤ) (hc : ∀ j, |c j| ≤ 1)
    (hsum : ∑ j ∈ range n, (3 : ℤ) ^ j * c j = 0) : ∀ j < n, c j = 0 := by
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
      rw [Finset.sum_range_succ] at hsum
      have hlead : (3 : ℤ) ^ n * c n = -∑ j ∈ range n, (3 : ℤ) ^ j * c j := by linarith
      have habs : |(3 : ℤ) ^ n * c n| < 3 ^ n := by
        rw [hlead, abs_neg]
        exact abs_sum_lt_pow n c hc
      have hcn : c n = 0 := by
        by_contra hne
        have h1 : 1 ≤ |c n| := by
          rcases lt_trichotomy (c n) 0 with h | h | h
          · rw [abs_of_neg h]; omega
          · exact absurd h hne
          · rw [abs_of_pos h]; omega
        have h2 : (3 : ℤ) ^ n ≤ |(3 : ℤ) ^ n * c n| := by
          rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 3)]
          calc (3 : ℤ) ^ n = 3 ^ n * 1 := (mul_one _).symm
            _ ≤ 3 ^ n * |c n| := mul_le_mul_of_nonneg_left h1 (by positivity)
        linarith
      have hrest : ∑ j ∈ range n, (3 : ℤ) ^ j * c j = 0 := by
        rw [hcn, mul_zero, add_zero] at hsum
        exact hsum
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact ih hrest j hlt
      · rw [heq]; exact hcn

/-- **The signed sums of powers of three are pairwise distinct.** -/
theorem sum_pow_three_sign_injOn (n : ℕ) {ε δ : ℕ → ℤ}
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (hδ : ∀ j, δ j = 1 ∨ δ j = -1)
    (h : ∑ j ∈ range n, (3 : ℤ) ^ j * ε j = ∑ j ∈ range n, (3 : ℤ) ^ j * δ j) :
    ∀ j < n, ε j = δ j := by
  classical
  set c : ℕ → ℤ := fun j => if ε j = δ j then 0 else if ε j = 1 then 1 else -1 with hcdef
  have hdiff : ∀ j, ε j - δ j = 2 * c j := by
    intro j
    rcases hε j with h1 | h1 <;> rcases hδ j with h2 | h2 <;>
      simp [hcdef, h1, h2]
  have hcabs : ∀ j, |c j| ≤ 1 := by
    intro j
    show |if ε j = δ j then (0 : ℤ) else if ε j = 1 then 1 else -1| ≤ 1
    split_ifs <;> norm_num
  have hzero : ∑ j ∈ range n, (3 : ℤ) ^ j * c j = 0 := by
    have hsub : ∑ j ∈ range n, (3 : ℤ) ^ j * (ε j - δ j) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [h, sub_self]
    have htwo : ∑ j ∈ range n, (3 : ℤ) ^ j * (ε j - δ j)
        = 2 * ∑ j ∈ range n, (3 : ℤ) ^ j * c j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hdiff j]; ring
    rw [htwo] at hsub
    linarith
  intro j hj
  have := eq_zero_of_sum_eq_zero n c hcabs hzero j hj
  have hd := hdiff j
  rw [this, mul_zero] at hd
  linarith [sub_eq_zero.mp hd]

end BalancedTernary

end GaloisForLFunctions.HTGeometry
