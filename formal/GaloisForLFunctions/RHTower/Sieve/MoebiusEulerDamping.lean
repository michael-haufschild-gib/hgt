import GaloisForLFunctions.RHTower.Sieve.EulerIntegerIndex

/-!
# The damping bound for the Möbius function

The Möbius function satisfies every hypothesis of the damped Dirichlet bound: it is multiplicative on
coprime arguments, `μ(1) = 1`, and `|μ| ≤ 1`.  Since `μ(p) = -1` at every prime, its distance from
the character `n^{it}` is

`D(μ,t;P)² = ∑_{p ∈ P} (1 + cos(t log p))/p`,

so the `∑_{p} 1/p` in the damping exponent cancels exactly and

`‖∑_{n squarefree, P-smooth} μ(n) n^{-it}/n‖ ≤ exp(∑_{p ∈ P} 1/p² - ∑_{p ∈ P} cos(t log p)/p)`.

At `t = 0` the right side is `exp(∑ 1/p² - ∑ 1/p)`, which tends to zero as `P` exhausts the primes:
the elementary cancellation of `μ` over squarefree smooth numbers, with an explicit rate.  For
`t ≠ 0` the bound is only as good as the lower bound available for `∑_p cos(t log p)/p`, and that is
where the elementary theory stops.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The Möbius function as a complex-valued function. -/
noncomputable def moebiusC (n : ℕ) : ℂ := (((moebius n : ℤ) : ℝ) : ℂ)

theorem abs_moebius_le_one (n : ℕ) : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
  rcases eq_or_ne (moebius n) 0 with h | h
  · simp [h]
  · rcases moebius_ne_zero_iff_eq_or.mp h with h1 | h1 <;> simp [h1]

theorem norm_moebiusC_le_one (n : ℕ) : ‖moebiusC n‖ ≤ 1 := by
  rw [moebiusC, Complex.norm_real, Real.norm_eq_abs]
  exact abs_moebius_le_one n

theorem moebiusC_one : moebiusC 1 = 1 := by simp [moebiusC]

theorem moebiusC_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    moebiusC (a * b) = moebiusC a * moebiusC b := by
  rw [moebiusC, moebiusC, moebiusC, isMultiplicative_moebius.map_mul_of_coprime h]
  push_cast
  ring

/-- At a prime the Möbius function is `-1`. -/
theorem moebiusC_prime {p : ℕ} (hp : p.Prime) : moebiusC p = -1 := by
  rw [moebiusC, moebius_apply_prime hp]
  norm_num

/-- **The Möbius distance from a character.** -/
theorem mulDistSq_moebiusC (t : ℝ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    mulDistSq moebiusC t P = ∑ p ∈ P, (1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [moebiusC_prime (hP p hp), neg_one_mul, Complex.neg_re,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- **The damped Möbius sum over squarefree `P`-smooth integers.** -/
theorem norm_sum_moebius_smooth_le_exp (t : ℝ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ‖∑ n ∈ P.powerset.image (fun T => ∏ p ∈ T, p), ((1 / (n : ℝ) : ℝ) : ℂ)
        * (moebiusC n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ) ^ 2)
          - ∑ p ∈ P, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) := by
  refine le_trans (norm_sum_smooth_le_exp norm_moebiusC_le_one
    (fun a b h => moebiusC_mul_of_coprime h) moebiusC_one t hP) ?_
  refine Real.exp_le_exp.mpr ?_
  rw [mulDistSq_moebiusC t hP]
  have hsplit : ∑ p ∈ P, (1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ)
      = (∑ p ∈ P, 1 / (p : ℝ)) + ∑ p ∈ P, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit]
  linarith

end RHTower.Sieve
