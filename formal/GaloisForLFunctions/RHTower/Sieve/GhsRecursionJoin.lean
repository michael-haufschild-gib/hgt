import GaloisForLFunctions.RHTower.Sieve.ConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.Sieve.GhsCoefficients

/-!
# The double prime average is the summatory function of the triple convolution

The logarithmic recursion, applied twice, presents the partial sums of `f` through the double prime average

`∑_{p} f(p)·log p/log⌊N₀/p⌋ ∑_{q} f(q)·log q ∑_{k ≤ N/pq} f(k)`,

the outer sum over primes `p ≤ N` with `⌊N₀/p⌋ ≥ 2` and the inner over primes `q ≤ min(N/p, M)`.  The
Perron and mean-square steps, on the other hand, estimate the summatory function of the Dirichlet
convolution `a ⍟ (b ⍟ f)` of the two prime weights with `f`.  The two are equal, with no hypothesis: the
summatory swap turns the convolution into an iterated sum, and each prime weight vanishes off its support,
so the sums over all integers collapse to the sums over primes.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- Summing a weight that vanishes off a predicate is summing over the predicate. -/
theorem sum_ghsOuter_mul_eq_filter {f : ℕ → ℂ} (N₀ : ℕ) (s : Finset ℕ) (X : ℕ → ℂ) :
    (∑ p ∈ s, ghsOuter f N₀ p * X p)
      = ∑ p ∈ {p ∈ s | Nat.Prime p ∧ 2 ≤ N₀ / p},
          f p * ((Real.log p / Real.log ((N₀ / p : ℕ) : ℝ) : ℝ) : ℂ) * X p := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (fun p => Nat.Prime p ∧ 2 ≤ N₀ / p)]
  have hzero : (∑ p ∈ {p ∈ s | ¬(Nat.Prime p ∧ 2 ≤ N₀ / p)}, ghsOuter f N₀ p * X p) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [ghsOuter, if_neg hp.2, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [ghsOuter, if_pos hp.2]

/-- Summing the inner weight is summing over the primes it is carried by. -/
theorem sum_ghsInner_mul_eq_filter {f : ℕ → ℂ} (M : ℕ) (s : Finset ℕ) (X : ℕ → ℂ) :
    (∑ q ∈ s, ghsInner f M q * X q)
      = ∑ q ∈ {q ∈ s | Nat.Prime q ∧ q ≤ M}, f q * ((Real.log q : ℝ) : ℂ) * X q := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (fun q => Nat.Prime q ∧ q ≤ M)]
  have hzero : (∑ q ∈ {q ∈ s | ¬(Nat.Prime q ∧ q ≤ M)}, ghsInner f M q * X q) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.mem_filter] at hq
    rw [ghsInner, if_neg hq.2, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [ghsInner, if_pos hq.2]

/-- **The two halves of the argument meet.**  The summatory function of the triple convolution *is* the
double prime average that two applications of the logarithmic recursion produce:

`∑_{n ≤ N} (a ⍟ (b ⍟ f))(n) = ∑_{p} f(p)·log p/log⌊N₀/p⌋ ∑_{q} f(q)·log q ∑_{k ≤ N/pq} f(k)`,

the outer sum over primes `p ≤ N` with `⌊N₀/p⌋ ≥ 2` and the inner over primes `q ≤ min(N/p, M)`.  No
hypothesis: the identity is the summatory swap together with the vanishing of the two weights off their
supports. -/
theorem sum_Icc_ghsTriple_eq_prime_double_average (f : ℕ → ℂ) (N₀ M N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuter f N₀) (LSeries.convolution (ghsInner f M) f)) n)
      = ∑ p ∈ {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N₀ / p},
          f p * ((Real.log p / Real.log ((N₀ / p : ℕ) : ℝ) : ℝ) : ℂ)
            * ∑ q ∈ {q ∈ Finset.Icc 1 (N / p) | Nat.Prime q ∧ q ≤ M},
                f q * ((Real.log q : ℝ) : ℂ) * ∑ k ∈ Finset.Icc 1 (N / p / q), f k := by
  classical
  rw [sum_Icc_convolution_triple_apply (ghsOuter f N₀) (ghsInner f M) f N]
  rw [sum_ghsOuter_mul_eq_filter N₀ (Finset.Icc 1 N)
    (fun p => ∑ q ∈ Finset.Icc 1 (N / p), ghsInner f M q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_ghsInner_mul_eq_filter M (Finset.Icc 1 (N / p))
    (fun q => ∑ k ∈ Finset.Icc 1 (N / p / q), f k)]

end RHTower.Sieve
end
