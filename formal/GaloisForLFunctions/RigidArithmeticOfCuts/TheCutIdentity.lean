import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The cut identity

Summation by parts against the sawtooth `r mod k`. If `U(r) = T(r) − T(r + 1)`, then

`Σ_{r ≤ kJ} U(r) (r mod k) = Σ_{r ≤ kJ} T(r) − k Σ_{j ≤ J} T(kj)`.

Each integer contributes `T(r)`, and a multiple of `k` subtracts `k T(r)`: the sawtooth rises by `1`
except at its cut, where it falls by `k − 1`. This is the single algebraic fact behind the cut system.
Reading `T(r) = ψ(n/r)/n` makes the left side a Chebyshev moment and the right side a statement about
the multiples of `k` alone.
-/

open Finset

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable {R : Type*} [CommRing R]

/-- The rise of the sawtooth: `+1`, and `−(k − 1)` at a cut. -/
private lemma natCast_succ_mod {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    (((N + 1) % k : ℕ) : R) = ((N % k : ℕ) : R) + 1 - if k ∣ N + 1 then (k : R) else 0 := by
  have hdiv := Nat.div_add_mod N k
  have hlt := Nat.mod_lt N (by omega : 0 < k)
  split_ifs with h
  · have hd : k ∣ N % k + 1 := by
      have hN : N + 1 = k * (N / k) + (N % k + 1) := by omega
      rw [hN] at h
      exact (Nat.dvd_add_right (dvd_mul_right k (N / k))).mp h
    have hle := Nat.le_of_dvd (by omega) hd
    have heq : N % k + 1 = k := by omega
    have heqR : ((N % k : ℕ) : R) + 1 = (k : R) := by
      have := congrArg (Nat.cast : ℕ → R) heq
      rwa [Nat.cast_add, Nat.cast_one] at this
    rw [Nat.mod_eq_zero_of_dvd h]
    push_cast
    linear_combination -heqR
  · have hne : N % k + 1 ≠ k := fun he => h (by
      have hN : N + 1 = k * (N / k) + k := by omega
      rw [hN]
      exact Nat.dvd_add (dvd_mul_right _ _) dvd_rfl)
    have hN : N + 1 = N % k + 1 + k * (N / k) := by omega
    have hmod : (N + 1) % k = N % k + 1 := by
      rw [hN, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    push_cast
    ring

/-- The cut identity at a general endpoint. -/
theorem sum_Icc_mul_mod (T : ℕ → R) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ∑ r ∈ Icc 1 N, (T r - T (r + 1)) * ((r % k : ℕ) : R) =
      ∑ r ∈ Icc 1 N, T r - (k : R) * ∑ j ∈ Icc 1 (N / k), T (k * j) -
        T (N + 1) * ((N % k : ℕ) : R) := by
  induction N with
  | zero => simp [Nat.zero_div]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      natCast_succ_mod hk N]
    by_cases h : k ∣ N + 1
    · have hdiv : (N + 1) / k = N / k + 1 := by
        rw [Nat.succ_div, if_pos h]
      have hprod : k * (N / k + 1) = N + 1 := by
        rw [← hdiv]
        exact Nat.mul_div_cancel' h
      rw [hdiv, sum_Icc_succ_top (Nat.le_add_left 1 _), hprod, if_pos h]
      ring
    · have hdiv : (N + 1) / k = N / k := by
        rw [Nat.succ_div, if_neg h, add_zero]
      rw [hdiv, if_neg h]
      ring

/-- **The cut identity.** Along multiples of `k` the boundary term vanishes. -/
theorem sum_Icc_mul_mod_mul (T : ℕ → R) {k : ℕ} (hk : 1 ≤ k) (J : ℕ) :
    ∑ r ∈ Icc 1 (k * J), (T r - T (r + 1)) * ((r % k : ℕ) : R) =
      ∑ r ∈ Icc 1 (k * J), T r - (k : R) * ∑ j ∈ Icc 1 J, T (k * j) := by
  rw [sum_Icc_mul_mod T hk, Nat.mul_div_cancel_left J (by omega : 0 < k), Nat.mul_mod_right]
  simp

/-- Reindex a sum over `[1, N]` by `j ↦ j + 1`. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ r ∈ Icc 1 N, f r = ∑ j ∈ range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

end GaloisForLFunctions.RigidArithmeticOfCuts
