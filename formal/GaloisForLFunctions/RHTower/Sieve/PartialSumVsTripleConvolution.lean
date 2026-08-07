import GaloisForLFunctions.RHTower.Sieve.SecondLogRecursion
import GaloisForLFunctions.RHTower.Sieve.GhsRecursionJoin
import GaloisForLFunctions.RHTower.Sieve.Mertens
import GaloisForLFunctions.RHTower.Sieve.PrimeLogSqLower
/-!
# The partial sum against the summatory function of the triple convolution

Two applications of the logarithmic recursion, with their errors evaluated, give

`‖(∑_{n ≤ N} f(n))·log N − ∑_{n ≤ N} (a ⍟ (b ⍟ f))(n)‖
    ≤ (9+c)N + N log 4 + (9+c)·N·(B/log 2)·(1 + log log₂ N)`

for the two prime weights of the argument, with `a` cut at `N` and `b` cut at `N` as well — at that choice
the inner truncation is vacuous, since the inner primes already satisfy `q ≤ N/p ≤ N`.

Three errors enter, all `O(N log log N)`: the first recursion contributes `(9+c)N`; the primes above `N/2`,
whose inner partial sum is the single term `f(1)`, contribute at most Chebyshev's `N log 4`; and the second
recursion contributes `(9+c)N` times the dyadic quotient-window estimate.

The left-hand object is what a mean value theorem is about, and the right-hand object is what the Perron and
mean-square steps estimate; the two are the same up to an error smaller than the main term by a full
logarithm divided by `log log`.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

variable {f : ℕ → ℂ}

/-- The primes whose complementary scale is below `2` contribute at most Chebyshev's bound: their inner
partial sum is the single term `f(1)`. -/
theorem norm_sum_prime_head_le (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ ¬(2 ≤ N / p)),
        ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k‖
      ≤ (N : ℝ) * Real.log 4 := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ Finset.filter (fun p => Nat.Prime p ∧ ¬(2 ≤ N / p)) (Finset.Icc 1 N),
      ‖((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k‖
        ≤ Real.log (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hpr, hlt⟩ := hp
    have hq1 : N / p = 1 := by
      have hle : 1 ≤ N / p := Nat.one_le_div_iff (by omega) |>.2 hpN
      omega
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := by
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
      exact Real.log_nonneg this
    rw [hq1]
    have hone : (∑ k ∈ Finset.Icc 1 1, f k) = f 1 := by simp
    rw [hone, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogp]
    calc Real.log (p : ℝ) * ‖f p‖ * ‖f 1‖
        ≤ Real.log (p : ℝ) * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hbdd p) hlogp) (hbdd 1) (norm_nonneg _)
            (by positivity)
      _ = Real.log (p : ℝ) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsub : Finset.filter (fun p => Nat.Prime p ∧ ¬(2 ≤ N / p)) (Finset.Icc 1 N)
      ⊆ Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hmono : (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ ¬(2 ≤ N / p)) (Finset.Icc 1 N),
        Real.log (p : ℝ))
      ≤ ∑ p ∈ Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N), Real.log (p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.1
    exact Real.log_nonneg this
  refine le_trans hmono ?_
  rw [filter_prime_Icc_eq_primesLE]
  exact sum_log_primesLE_le N

/-- **Steps one and two together.**  The partial sum times `log N` is the double prime average up to
`O(N log log N)`: Chebyshev's bound absorbs the primes above `N/2`, whose inner sum is a single term. -/
theorem norm_sum_Icc_mul_log_sub_double_prime_average_le
    (hf : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) (hN : 2 ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
            ((Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) * f p
              * ∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                  ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k‖
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
        + (9 + RHTower.Mertens.mertensTail)
            * ((N : ℝ)
                * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                      / Real.log 2)
                    * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))) := by
  classical
  set S : ℂ := (∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ) with hS
  set P : ℂ := ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
      ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k with hP
  set Ptail : ℂ := ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
      ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k with hPtail
  set Phead : ℂ := ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ ¬(2 ≤ N / p)),
      ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k with hPhead
  set D : ℂ := ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
      ((Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) * f p
        * ∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
            ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k with hD
  have hsplit : P = Ptail + Phead := by
    rw [hP, hPtail, hPhead]
    have h := Finset.sum_filter_add_sum_filter_not
      (Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N)) (fun p => 2 ≤ N / p)
      (fun p => ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k)
    rw [Finset.filter_filter, Finset.filter_filter] at h
    exact h.symm
  have h1 := norm_sum_Icc_mul_log_sub_sum_primes_le' hf hbdd N
  have h2 := norm_sum_primes_sub_double_prime_average_le_explicit hf hbdd N hN
  have hhead := norm_sum_prime_head_le hbdd N
  have hdiff : Ptail - D = ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
      (((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k
        - ((Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) * f p
            * ∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k) := by
    rw [hPtail, hD, ← Finset.sum_sub_distrib]
  have h2' : ‖Ptail - D‖
      ≤ (9 + RHTower.Mertens.mertensTail)
          * ((N : ℝ)
              * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                    / Real.log 2)
                  * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))) := by
    rw [hdiff]
    exact h2
  have hchain : S - D = (S - P) + Phead + (Ptail - D) := by
    rw [hsplit]
    ring
  rw [hchain]
  have hstep := norm_add_le ((S - P) + Phead) (Ptail - D)
  have hstep2 := norm_add_le (S - P) Phead
  have h1' : ‖S - P‖ ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
    rw [hS, hP]
    exact h1
  have hhead' : ‖Phead‖ ≤ (N : ℝ) * Real.log 4 := by
    rw [hPhead]
    exact hhead
  linarith [hstep, hstep2, h1', hhead', h2']

/-- At `N₀ = M = N` the inner truncation is vacuous, so the summatory function of the triple convolution is
the double prime average of the recursion verbatim. -/
theorem sum_Icc_ghsTriple_self_eq (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
      = ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
          ((Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) * f p
            * ∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k := by
  classical
  rw [sum_Icc_ghsTriple_eq_prime_double_average f N N N]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hfilter : Finset.filter (fun q => Nat.Prime q ∧ q ≤ N) (Finset.Icc 1 (N / p))
      = Finset.filter (fun q => Nat.Prime q) (Finset.Icc 1 (N / p)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      exact ⟨h.1, h.2, le_trans h.1.2 (Nat.div_le_self N p)⟩
  rw [hfilter]
  have hinner : (∑ q ∈ Finset.filter (fun q => Nat.Prime q) (Finset.Icc 1 (N / p)),
        f q * ((Real.log (q : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
      = ∑ q ∈ Finset.filter (fun q => Nat.Prime q) (Finset.Icc 1 (N / p)),
          ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k :=
    Finset.sum_congr rfl fun q _ => by ring
  rw [hinner]
  ring

/-- **Steps one to three, in the language of step four.**  The partial sum times `log N` is the summatory
function of the triple convolution up to `O(N log log N)`:

`‖(∑_{n ≤ N} f(n))·log N − ∑_{n ≤ N} (a ⍟ (b ⍟ f))(n)‖ ≤ (9+c)N + N log 4 + (9+c)·N·(B/log 2)(1 + log log₂ N)`.

The left-hand object is what a mean value theorem is about; the right-hand object is what the Perron and
mean-square steps estimate. -/
theorem norm_sum_Icc_mul_log_sub_ghsTriple_le
    (hf : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) (hN : 2 ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ n ∈ Finset.Icc 1 N,
            (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
        + (9 + RHTower.Mertens.mertensTail)
            * ((N : ℝ)
                * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                      / Real.log 2)
                    * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))) := by
  rw [sum_Icc_ghsTriple_self_eq f N]
  exact norm_sum_Icc_mul_log_sub_double_prime_average_le hf hbdd N hN

end RHTower.Sieve
end
