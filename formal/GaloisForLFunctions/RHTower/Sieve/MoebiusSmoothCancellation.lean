import GaloisForLFunctions.RHTower.Sieve.MoebiusEulerDamping
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic

/-!
# Unconditional cancellation of μ over squarefree smooth numbers

The inverse-square sum over any finite set of primes is bounded by an absolute constant, so the
damping exponent loses its `∑ 1/p²` term:

`‖∑_{n squarefree, P-smooth} μ(n) n^{-it}/n‖ ≤ exp(2 - ∑_{p ∈ P} cos(t log p)/p)`.

At `t = 0` this is

`‖∑_{n squarefree, P-smooth} μ(n)/n‖ ≤ exp(2 - ∑_{p ∈ P} 1/p)`,

an unconditional bound with an explicit rate: since `∑_p 1/p` diverges, the left side tends to zero
as `P` exhausts the primes.  For `t ≠ 0` nothing of the kind follows from this alone — the exponent
is governed by `∑_p cos(t log p)/p`, and a lower bound for it uniform in `t` is the non-elementary
input.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The inverse-square sum over a finite set of positive integers is at most `2`. -/
theorem sum_inv_sq_le_two_of_pos {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) :
    ∑ p ∈ P, 1 / (p : ℝ) ^ 2 ≤ 2 := by
  classical
  have hsub : P ⊆ Finset.Icc 1 (P.sup id) := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨hP p hp, Finset.le_sup (f := id) hp⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity) ?_
  exact sum_inv_sq_le_two (P.sup id)

/-- **The damped Möbius sum, with an absolute constant.** -/
theorem norm_sum_moebius_smooth_le_exp_two (t : ℝ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ‖∑ n ∈ P.powerset.image (fun T => ∏ p ∈ T, p), ((1 / (n : ℝ) : ℝ) : ℂ)
        * (moebiusC n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
      ≤ Real.exp (2 - ∑ p ∈ P, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) := by
  refine le_trans (norm_sum_moebius_smooth_le_exp t hP) (Real.exp_le_exp.mpr ?_)
  have := sum_inv_sq_le_two_of_pos fun p hp => (hP p hp).pos
  linarith

/-- **Unconditional cancellation of μ over squarefree `P`-smooth numbers.** -/
theorem norm_sum_moebius_smooth_zero_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ‖∑ n ∈ P.powerset.image (fun T => ∏ p ∈ T, p), ((1 / (n : ℝ) : ℝ) : ℂ) * moebiusC n‖
      ≤ Real.exp (2 - ∑ p ∈ P, 1 / (p : ℝ)) := by
  have h := norm_sum_moebius_smooth_le_exp_two 0 hP
  have hcos : ∀ p ∈ P, Real.cos (0 * Real.log (p : ℝ)) / (p : ℝ) = 1 / (p : ℝ) := by
    intro p _
    norm_num
  rw [Finset.sum_congr rfl hcos] at h
  simpa using h

end RHTower.Sieve
