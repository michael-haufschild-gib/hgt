import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! A weighted sum of Gaussian binomial coefficients for the identity character value. -/

namespace GlobalTheory.QBinomialSum

private lemma prod_succ_succ (x : ℂ) (n a : ℕ) :
    ∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)
      = (x ^ (n + 1) - 1) * x ^ a * ∏ i ∈ Finset.range a, (x ^ n - x ^ i) := by
  rw [Finset.prod_range_succ']
  have hf (i : ℕ) : x ^ (n + 1) - x ^ (i + 1) = x * (x ^ n - x ^ i) := by ring
  simp only [hf, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, pow_zero]
  ring

private lemma denominator_ne_zero (x : ℂ) (hx : x ≠ 0)
    (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (a : ℕ) :
    ∏ i ∈ Finset.range a, (x ^ a - x ^ i) ≠ 0 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [prod_succ_succ]
    exact mul_ne_zero (mul_ne_zero (h1 a) (pow_ne_zero _ hx)) ih

private lemma sum_eq (x : ℂ) (hx : x ≠ 0) (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (n : ℕ) :
    ∑ a ∈ Finset.range n,
      (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    let c (a : ℕ) := (∏ i ∈ Finset.range a, (x ^ n - x ^ i)) /
      (∏ i ∈ Finset.range a, (x ^ a - x ^ i)) * ∏ i ∈ Finset.range a, (1 - x ^ (i + 1))
    -- The change in the summand from dimension n to n+1 telescopes.
    have step (a : ℕ) :
        (∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)) /
          (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
          ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) =
        (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
          (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
          (∏ i ∈ Finset.range a, (1 - x ^ (i + 1))) + (c a - c (a + 1)) := by
      dsimp only [c]
      rw [prod_succ_succ x n a, prod_succ_succ x a a,
        Finset.prod_range_succ (fun i => x ^ n - x ^ i),
        Finset.prod_range_succ (fun i => 1 - x ^ (i + 1))]
      have hd := denominator_ne_zero x hx h1 a
      have h2 := h1 a
      have h3 := pow_ne_zero a hx
      generalize ∏ i ∈ Finset.range a, (x ^ a - x ^ i) = D at *
      generalize ∏ i ∈ Finset.range a, (x ^ n - x ^ i) = P
      generalize ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = W
      field_simp
      ring
    have hz : ∏ i ∈ Finset.range (n + 1), (x ^ n - x ^ i) = 0 :=
      Finset.prod_eq_zero (Finset.self_mem_range_succ n) (sub_self _)
    simp only [step]
    rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_succ, ih, hz]
    have hc₀ : c 0 = 1 := by simp [c]
    have hcₙ : c (n + 1) = 0 := by simp [c, hz]
    rw [hc₀, hcₙ]
    push_cast
    simp

/-- The weighted number of nonzero subspaces is the ambient dimension. -/
theorem sum_gaussian_mul_prod (q n : ℕ) (N : ℕ → ℕ) (hq : 2 ≤ q)
    (hN : ∀ a, a ≤ n → N a * ∏ i ∈ Finset.range a, (q ^ a - q ^ i) =
      ∏ i ∈ Finset.range a, (q ^ n - q ^ i)) :
    ∑ a ∈ Finset.Icc 1 n, (N a : ℂ) * ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i) = n := by
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hq₁ (k : ℕ) : (q : ℂ) ^ (k + 1) - 1 ≠ 0 := by
    intro h
    have he : q ^ (k + 1) = 1 := by exact_mod_cast (sub_eq_zero.mp h)
    have hp := Nat.one_lt_pow (n := k + 1) (a := q) (by omega) (by omega)
    omega
  have cast_prod (m a : ℕ) (ha : a ≤ m) : ((∏ i ∈ Finset.range a, (q ^ m - q ^ i) : ℕ) : ℂ)
      = ∏ i ∈ Finset.range a, ((q : ℂ) ^ m - (q : ℂ) ^ i) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (by omega))]
    push_cast
    rfl
  rw [← sum_eq (q : ℂ) hq₀ hq₁ n, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.mp ha
  rw [Finset.prod_Ico_eq_prod_range, add_comm 1 a]
  simp only [Nat.add_sub_cancel]
  have h := congrArg (Nat.cast : ℕ → ℂ) (hN (a + 1) (by omega))
  rw [Nat.cast_mul, cast_prod _ _ le_rfl, cast_prod _ _ (by omega)] at h
  rw [← h, mul_div_cancel_right₀ _ (denominator_ne_zero _ hq₀ hq₁ (a + 1))]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [add_comm]

end GlobalTheory.QBinomialSum
