import GaloisForLFunctions.RHTower.Sieve.PairEulerFactor
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange

/-!
# The Mertens product from below

The sieve saving is the reciprocal of `∏_{p ∈ s} p/(p−1)`, and a lower bound for that product needs
no error term at all: `1 − x ≤ e^{-x}` gives `e^{1/p} ≤ p/(p−1)` at every prime, so the product is
at least the exponential of the prime harmonic sum over the range.

Over a range of primes that sum is a difference of two Mertens sums, so the whole bound is
`exp(mertensS h − mertensS P₁)`, which is the ratio `log h / log P₁` up to the Mertens constant.
-/

namespace RHTower.Sieve

open Finset

/-- `e^{1/p} ≤ p/(p−1)`, from `1 − x ≤ e^{-x}`. -/
theorem exp_inv_le_ratio {p : ℕ} (hp : 2 ≤ p) :
    Real.exp (1 / (p : ℝ)) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hkey : (1 : ℝ) - 1 / (p : ℝ) ≤ Real.exp (-(1 / (p : ℝ))) := Real.one_sub_le_exp_neg _
  have hval : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
    field_simp
  rw [hval, Real.exp_neg] at hkey
  have hexp0 : (0 : ℝ) < Real.exp (1 / (p : ℝ)) := Real.exp_pos _
  rw [le_inv_comm₀ (by positivity) hexp0, inv_div] at hkey
  exact hkey

/-- **The Mertens product dominates the exponential of the prime harmonic sum.** -/
theorem exp_sum_inv_le_prod {s : Finset ℕ} (hs : ∀ p ∈ s, 2 ≤ p) :
    Real.exp (∑ p ∈ s, 1 / (p : ℝ)) ≤ ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p hp => exp_inv_le_ratio (hs p hp)

/-- The two descriptions of a range of primes agree. -/
theorem rangePrimes_eq_primesRange (P₁ h : ℕ) : rangePrimes P₁ h = primesRange P₁ h := by
  classical
  ext p
  rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc, primesRange, Finset.mem_sdiff,
    mem_primesLE, mem_primesLE]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨h2, hp⟩, fun hc => by omega⟩
  · rintro ⟨⟨h2, hp⟩, hnot⟩
    refine ⟨⟨?_, h2⟩, hp⟩
    by_contra hc
    exact hnot ⟨by omega, hp⟩

/-- **The sieve's Mertens product, from below.** -/
theorem prod_rangePrimes_ge (P₁ h : ℕ) (hP₁ : P₁ ≤ h) :
    Real.exp (mertensS h - mertensS P₁)
      ≤ ∏ p ∈ rangePrimes P₁ h, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hs : ∀ p ∈ rangePrimes P₁ h, 2 ≤ p := by
    intro p hp
    exact (rangePrimes_prime hp).two_le
  refine le_trans (le_of_eq ?_) (exp_sum_inv_le_prod hs)
  congr 1
  rw [rangePrimes_eq_primesRange, sum_inv_primesRange hP₁]

end RHTower.Sieve
