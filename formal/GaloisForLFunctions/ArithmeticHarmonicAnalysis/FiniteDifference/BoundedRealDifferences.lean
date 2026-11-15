import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Bounded real sequences with vanishing differences

A bounded real sequence with constant first difference has zero first
difference. Induction applies this observation to every order. An interval
of width `D` bounds the difference of order `n+1` by `2^n D`.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Function

/-- An interval bound controls every positive order real finite difference. -/
theorem real_iterated_difference_interval_bound (f : ℕ → ℝ) (L D : ℝ)
    (hb : ∀ j, L ≤ f j ∧ f j ≤ L + D) (n j : ℕ) :
    -(2 ^ n * D) ≤ (fwdDiff 1)^[n + 1] f j ∧
      (fwdDiff 1)^[n + 1] f j ≤ 2 ^ n * D := by
  induction n generalizing j with
  | zero =>
    simp only [Nat.zero_add, pow_zero, one_mul, iterate_one, fwdDiff]
    have h0 := hb j
    have h1 := hb (j + 1)
    constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2]
  | succ n ih =>
    rw [iterate_succ_apply']
    change -(2 ^ (n + 1) * D) ≤
        (fwdDiff 1)^[n + 1] f (j + 1) - (fwdDiff 1)^[n + 1] f j ∧
      (fwdDiff 1)^[n + 1] f (j + 1) - (fwdDiff 1)^[n + 1] f j ≤ 2 ^ (n + 1) * D
    have h0 := ih j
    have h1 := ih (j + 1)
    rw [pow_succ]
    constructor <;> nlinarith only [h0.1, h0.2, h1.1, h1.2]

private theorem real_constant_of_difference_zero (f : ℕ → ℝ)
    (h : fwdDiff 1 f = 0) : ∀ j, f j = f 0 := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have hs := congrFun h j
    change f (j + 1) - f j = 0 at hs
    linarith only [hs, ih]

private theorem bounded_real_constant_of_constant_difference (f : ℕ → ℝ) (L D : ℝ)
    (hb : ∀ j, L ≤ f j ∧ f j ≤ L + D)
    (hd : ∀ j, fwdDiff 1 f j = fwdDiff 1 f 0) : ∀ j, f j = f 0 := by
  have hp (j : ℕ) : f j = f 0 + (j : ℝ) * (f 1 - f 0) := by
    induction j with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]
    | succ j ih =>
      have he := hd j
      change f (j + 1) - f j = f 1 - f 0 at he
      rw [Nat.cast_add, Nat.cast_one]
      linear_combination ih + he
  have hz : f 1 - f 0 = 0 := by
    rcases lt_trichotomy (f 1 - f 0) 0 with hn | hz | hn
    · obtain ⟨j, hj⟩ := exists_nat_gt (D / -(f 1 - f 0))
      have hm := (div_lt_iff₀ (neg_pos.mpr hn)).mp hj
      have h0 := hb 0
      have hj' := hb j
      have he := hp j
      nlinarith only [hm, h0.2, hj'.1, he]
    · exact hz
    · obtain ⟨j, hj⟩ := exists_nat_gt (D / (f 1 - f 0))
      have hm := (div_lt_iff₀ hn).mp hj
      have h0 := hb 0
      have hj' := hb j
      have he := hp j
      nlinarith only [hm, h0.1, hj'.2, he]
  intro j
  simpa only [hz, mul_zero, add_zero] using hp j

/-- A bounded real sequence with vanishing difference of positive order is constant. -/
theorem bounded_real_iterated_difference_zero_iff (f : ℕ → ℝ) (L D : ℝ)
    (hb : ∀ j, L ≤ f j ∧ f j ≤ L + D) (n : ℕ) :
    (fwdDiff 1)^[n + 1] f = 0 ↔ ∀ j, f j = f 0 := by
  constructor
  · intro hz
    induction n generalizing f L D with
    | zero => exact real_constant_of_difference_zero f hz
    | succ n ih =>
      have hbg : ∀ j, -D ≤ fwdDiff 1 f j ∧ fwdDiff 1 f j ≤ -D + 2 * D := by
        intro j
        have he := real_iterated_difference_interval_bound f L D hb 0 j
        simp only [Nat.zero_add, pow_zero, one_mul, iterate_one] at he
        constructor <;> linarith only [he.1, he.2]
      have hc := ih (fwdDiff 1 f) (-D) (2 * D) hbg (by
        simpa only [iterate_succ_apply] using hz)
      exact bounded_real_constant_of_constant_difference f L D hb hc
  · intro hc
    rw [show f = fun _ => f 0 from funext hc, iterate_succ_apply, fwdDiff_const]
    have hz : ∀ m : ℕ, (fwdDiff (1 : ℕ))^[m] (fun _ => (0 : ℝ)) = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [iterate_succ_apply', ih]; exact funext fun _ => sub_self (0 : ℝ)
    exact hz n

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.real_iterated_difference_interval_bound
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.bounded_real_iterated_difference_zero_iff
