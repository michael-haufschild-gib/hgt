import GaloisForLFunctions.RHTower.Sieve.TripleConvolutionWindow

/-!
# Splitting the double prime average at a dyadic quotient threshold

The primes with a large quotient form an initial segment: `2^n ≤ ⌊N/p⌋ ↔ p ≤ ⌊N/2^n⌋`.  So the double
prime average of the recursion splits into

* its restriction to the initial segment `p ≤ ⌊N/2^n⌋` — the range where the inner Dirichlet polynomials
  are long and the analytic estimate applies, and
* a remainder over `2 ≤ ⌊N/p⌋ < 2^n`, whose trivial size is `O(N·n)` by the window bound.

This is the shape of the Granville–Harper–Soundararajan step 3 with the double-exponential blocks replaced
by a single dyadic quotient threshold: no summation over blocks is needed, because the window bound is
already additive in the number of dyadic scales it spans.  Choosing `n` of the order of the Halász
parameter makes the discarded remainder `O(N·L)`.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The primes with a large quotient form an initial segment. -/
theorem filter_large_quotient_eq {N n : ℕ} (hn : 1 ≤ n) :
    {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N / p ∧ 2 ^ n ≤ N / p}
      = {p ∈ Finset.Icc 1 (N / 2 ^ n) | Nat.Prime p} := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp1, hpN⟩, hprime, hq2, hqn⟩
    exact ⟨⟨hp1, (two_pow_le_div_iff hp1).1 hqn⟩, hprime⟩
  · rintro ⟨⟨hp1, hple⟩, hprime⟩
    have hqn : 2 ^ n ≤ N / p := (two_pow_le_div_iff hp1).2 hple
    have h2n : (2:ℕ) ≤ 2 ^ n := by
      calc (2:ℕ) = 2 ^ (1 : ℕ) := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hpN : p ≤ N := by
      have hdiv : N / 2 ^ n ≤ N := Nat.div_le_self N _
      omega
    exact ⟨⟨hp1, hpN⟩, hprime, le_trans h2n hqn, hqn⟩

/-- The prime range splits at a dyadic quotient threshold. -/
theorem sum_split_at_quotient_threshold {M : Type*} [AddCommMonoid M] (N n : ℕ) (g : ℕ → M) :
    (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p), g p)
      = (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p ∧ N / p < 2 ^ n), g p)
        + ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p ∧ 2 ^ n ≤ N / p), g p := by
  classical
  have hlow : {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N / p ∧ N / p < 2 ^ n}
      = {p ∈ ({p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N / p}) | N / p < 2 ^ n} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    tauto
  have hhigh : {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N / p ∧ 2 ^ n ≤ N / p}
      = {p ∈ ({p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N / p}) | ¬ (N / p < 2 ^ n)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
    tauto
  rw [hlow, hhigh]
  exact (Finset.sum_filter_add_sum_filter_not _ (fun p => N / p < 2 ^ n) g).symm


variable {f : ℕ → ℂ}

/-- The summand of the double prime average: the outer prime weight against the inner double sum. -/
def doubleAverageTerm (f : ℕ → ℂ) (N p : ℕ) : ℂ :=
  ((Real.log (p : ℝ) : ℝ) : ℂ) * f p
    * ((∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
          ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
        / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ))

/-- **Step 3.**  At a dyadic quotient threshold the double prime average is its restriction to an
initial segment of primes — the analytic regime, where `⌊N/p⌋ ≥ 2^n` — plus a remainder of trivial size
`O(N·n)`.  Choosing `n` of the order of the Halász parameter makes the remainder `O(N·L)`. -/
theorem norm_double_average_sub_initial_le (hbdd : ∀ k : ℕ, ‖f k‖ ≤ 1) (N : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖(∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p), doubleAverageTerm f N p)
        - ∑ p ∈ Finset.Icc 1 (N / 2 ^ n) with Nat.Prime p, doubleAverageTerm f N p‖
      ≤ (1 + ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) / Real.log 2) * (N : ℝ)
          * ((n : ℝ) * Real.log 2
              + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail))) := by
  classical
  have hsplit := sum_split_at_quotient_threshold (M := ℂ) N n (fun p => doubleAverageTerm f N p)
  have hhigh : {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N / p ∧ 2 ^ n ≤ N / p}
      = {p ∈ Finset.Icc 1 (N / 2 ^ n) | Nat.Prime p} := filter_large_quotient_eq hn
  rw [hhigh] at hsplit
  have hlowset : {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N / p ∧ N / p < 2 ^ n}
      = {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ^ (1 : ℕ) ≤ N / p ∧ N / p < 2 ^ n} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, pow_one]
  have hdiff : (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p), doubleAverageTerm f N p)
      - (∑ p ∈ Finset.Icc 1 (N / 2 ^ n) with Nat.Prime p, doubleAverageTerm f N p)
      = ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ^ (1 : ℕ) ≤ N / p ∧ N / p < 2 ^ n),
          doubleAverageTerm f N p := by
    rw [← hlowset]
    rw [hsplit]
    ring
  rw [hdiff]
  have hwin := norm_window_triple_le (f := f) hbdd N (m := 1) (n := n) le_rfl hn
  simp only [doubleAverageTerm]
  refine le_trans hwin (le_of_eq ?_)
  congr 2
  push_cast
  ring

end RHTower.Sieve
end
