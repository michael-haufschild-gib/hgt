import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The summatory function of a convolution of plain sequences

For sequences indexed by `ℕ` — not arithmetic functions, so with no condition at `0` —

`∑_{n ≤ N} (a ⍟ b)(n) = ∑_{d ≤ N} a_d ∑_{m ≤ N/d} b_m`,
`∑_{n ≤ N} (a ⍟ (b ⍟ c))(n) = ∑_{p ≤ N} a_p ∑_{q ≤ N/p} b_q ∑_{k ≤ N/p/q} c_k`.

Neither statement carries a hypothesis: a convolution evaluated at `n ≥ 1` never reads the value at `0`, so
the arithmetic-function swap of the corpus applies verbatim to the zero-extended sequences.

This is the identity that joins the two halves of the Granville–Harper–Soundararajan argument: its left side
is what the Perron and mean-square steps estimate, its right side is what two applications of the
logarithmic recursion produce.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **The summatory swap for a Dirichlet convolution of plain sequences.**  No hypothesis on the
sequences: the convolution at `n ≥ 1` never reads the value at `0`. -/
theorem sum_Icc_convolution_apply {R : Type*} [Semiring R] (a b : ℕ → R) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, LSeries.convolution a b n)
      = ∑ d ∈ Finset.Icc 1 N, a d * ∑ m ∈ Finset.Icc 1 (N / d), b m := by
  classical
  set A : ArithmeticFunction R := ⟨fun n => if n = 0 then 0 else a n, by simp⟩ with hA
  set B : ArithmeticFunction R := ⟨fun n => if n = 0 then 0 else b n, by simp⟩ with hB
  have hAval : ∀ n : ℕ, n ≠ 0 → A n = a n := by
    intro n hn
    rw [hA]
    simp [hn]
  have hBval : ∀ n : ℕ, n ≠ 0 → B n = b n := by
    intro n hn
    rw [hB]
    simp [hn]
  have hAB : ∀ n : ℕ, n ≠ 0 → (A * B) n = LSeries.convolution a b n := by
    intro n hn
    rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hx1 : x.1 ≠ 0 := by
      intro h
      rw [h, zero_mul] at hx
      exact hx.2 hx.1.symm
    have hx2 : x.2 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hx
      exact hx.2 hx.1.symm
    rw [hAval x.1 hx1, hBval x.2 hx2]
  have hleft : (∑ n ∈ Finset.Icc 1 N, LSeries.convolution a b n)
      = ∑ n ∈ Finset.Icc 1 N, (A * B) n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    exact (hAB n (by omega)).symm
  rw [hleft, RHTower.sum_Icc_mul_apply A B N]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [hAval d (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  exact hBval m (by omega)

/-- **The triple summatory swap for plain sequences.**  Two applications of the double swap: the summatory
function of `a ⍟ (b ⍟ c)` is the iterated sum over the two outer variables of the partial sums of `c`. -/
theorem sum_Icc_convolution_triple_apply {R : Type*} [Semiring R] (a b c : ℕ → R) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, LSeries.convolution a (LSeries.convolution b c) n)
      = ∑ p ∈ Finset.Icc 1 N, a p
          * ∑ q ∈ Finset.Icc 1 (N / p), b q * ∑ k ∈ Finset.Icc 1 (N / p / q), c k := by
  rw [sum_Icc_convolution_apply a (LSeries.convolution b c) N]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_Icc_convolution_apply b c (N / p)]

end RHTower.Sieve
end
