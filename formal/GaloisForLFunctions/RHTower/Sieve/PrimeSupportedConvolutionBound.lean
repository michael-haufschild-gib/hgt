import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A threefold convolution with prime-supported factors is polylogarithmic

A general threefold Dirichlet convolution has `d₃(n)` terms at `n`, and no polylogarithmic pointwise
bound.  But when two of the three factors are supported on the primes, a contributing factorisation
`n = pqk` is determined by a *pair of prime divisors* of `n`, so there are at most `ω(n)²` terms:

`‖(a ⍟ (b ⍟ c))(n)‖ ≤ ω(n)²·(log n)²`   for `‖a_p‖ ≤ log p`, `‖b_q‖ ≤ log q`, `‖c‖ ≤ 1`.

Since `ω(n) ≤ log n/log 2`, the coefficients are bounded by `(log n)⁴/(log 2)²` — polylogarithmic, with no
divisor function.  This is what makes every Perron passage for the Granville–Harper–Soundararajan triple
convolution elementary: the smoothing window and the near-diagonal block of a truncated contour both cost
a polylogarithm times their length, so no short-interval divisor estimate is needed.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The prime divisors are the prime divisors of the divisor set. -/
theorem filter_prime_divisors_eq_primeFactors {m : ℕ} (hm : m ≠ 0) :
    {q ∈ m.divisors | Nat.Prime q} = m.primeFactors := by
  classical
  ext q
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hp⟩
    exact ⟨hp, hdvd, hm⟩
  · rintro ⟨hp, hdvd, _⟩
    exact ⟨⟨hdvd, hm⟩, hp⟩

/-- **A prime-supported convolution factor is polylogarithmic.**  If `b` is supported on primes with
`‖b q‖ ≤ log q` and `‖c‖ ≤ 1`, then `‖(b ⍟ c)(m)‖ ≤ ω(m)·log m`: only the prime divisors of `m`
contribute, and each contributes at most `log m`. -/
theorem norm_convolution_prime_support_le_const {b c : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ q : ℕ, b q ≠ 0 → Nat.Prime q) (hbB : ∀ q : ℕ, ‖b q‖ ≤ B * Real.log q)
    (hc : ∀ k : ℕ, ‖c k‖ ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ‖(LSeries.convolution b c) m‖ ≤ B * ((m.primeFactors.card : ℝ) * Real.log m) := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : (0 : ℝ) ≤ Real.log m := Real.log_nonneg hmR
  have hexp : (LSeries.convolution b c) m = ∑ q ∈ m.divisors, b q * c (m / q) := by
    rw [LSeries.convolution_def]
    exact Nat.sum_divisorsAntidiagonal (fun q k => b q * c k)
  rw [hexp]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ q ∈ m.divisors,
      ‖b q * c (m / q)‖ ≤ (if Nat.Prime q then B * Real.log m else 0) := by
    intro q hq
    rw [Nat.mem_divisors] at hq
    by_cases hbq : b q = 0
    · rw [hbq, zero_mul, norm_zero]
      by_cases hp : Nat.Prime q
      · rw [if_pos hp]
        positivity
      · rw [if_neg hp]
    · have hp : Nat.Prime q := hb q hbq
      rw [if_pos hp, norm_mul]
      have hqm : q ≤ m := Nat.le_of_dvd (by omega) hq.1
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        have : 1 ≤ q := hp.one_lt.le.trans' (by norm_num)
        exact_mod_cast this
      have hlogq : Real.log q ≤ Real.log m := by
        refine Real.log_le_log (by linarith) ?_
        exact_mod_cast hqm
      calc ‖b q‖ * ‖c (m / q)‖ ≤ (B * Real.log q) * 1 :=
            mul_le_mul (hbB q) (hc _) (norm_nonneg _) (le_trans (norm_nonneg _) (hbB q))
        _ = B * Real.log q := mul_one _
        _ ≤ B * Real.log m := mul_le_mul_of_nonneg_left hlogq hB
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, Finset.sum_const, filter_prime_divisors_eq_primeFactors hm0,
    nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- The unit-constant case: `‖(b ⍟ c)(m)‖ ≤ ω(m)·log m`. -/
theorem norm_convolution_prime_support_le {b c : ℕ → ℂ}
    (hb : ∀ q : ℕ, b q ≠ 0 → Nat.Prime q) (hbB : ∀ q : ℕ, ‖b q‖ ≤ Real.log q)
    (hc : ∀ k : ℕ, ‖c k‖ ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ‖(LSeries.convolution b c) m‖ ≤ (m.primeFactors.card : ℝ) * Real.log m := by
  simpa using
    norm_convolution_prime_support_le_const (B := 1) zero_le_one hb (by simpa using hbB) hc hm

/-- **The triple convolution with two prime-supported factors is polylogarithmic.**  Only pairs of prime
divisors of `n` contribute, and each contributes at most `(log n)²`, so

`‖(a ⍟ (b ⍟ c))(n)‖ ≤ ω(n)²·(log n)²`.

There is no divisor function on the right: the prime support of two of the three factors collapses the
`d₃(n)` factorisations of a general threefold convolution to `ω(n)²` of them. -/
theorem norm_convolution_triple_prime_support_le_const {a b c : ℕ → ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ p : ℕ, a p ≠ 0 → Nat.Prime p) (haB : ∀ p : ℕ, ‖a p‖ ≤ A * Real.log p)
    (hb : ∀ q : ℕ, b q ≠ 0 → Nat.Prime q) (hbB : ∀ q : ℕ, ‖b q‖ ≤ B * Real.log q)
    (hc : ∀ k : ℕ, ‖c k‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖(LSeries.convolution a (LSeries.convolution b c)) n‖
      ≤ A * B * ((n.primeFactors.card : ℝ) ^ (2 : ℕ) * (Real.log n) ^ (2 : ℕ)) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  have hωnn : (0 : ℝ) ≤ (n.primeFactors.card : ℝ) := Nat.cast_nonneg _
  have hABnn : (0 : ℝ) ≤ A * B
      * ((n.primeFactors.card : ℝ) * Real.log n * Real.log n) :=
    mul_nonneg (mul_nonneg hA hB) (by positivity)
  have hexp : (LSeries.convolution a (LSeries.convolution b c)) n
      = ∑ p ∈ n.divisors, a p * (LSeries.convolution b c) (n / p) := by
    rw [LSeries.convolution_def]
    exact Nat.sum_divisorsAntidiagonal (fun p r => a p * (LSeries.convolution b c) r)
  rw [hexp]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ n.divisors,
      ‖a p * (LSeries.convolution b c) (n / p)‖
        ≤ (if Nat.Prime p then
              A * B * ((n.primeFactors.card : ℝ) * Real.log n * Real.log n) else 0) := by
    intro p hp
    rw [Nat.mem_divisors] at hp
    by_cases hap : a p = 0
    · rw [hap, zero_mul, norm_zero]
      by_cases hpr : Nat.Prime p
      · rw [if_pos hpr]
        exact hABnn
      · rw [if_neg hpr]
    · have hpr : Nat.Prime p := ha p hap
      rw [if_pos hpr, norm_mul]
      have hpn : p ≤ n := Nat.le_of_dvd (by omega) hp.1
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
        have : 1 ≤ p := hpr.one_lt.le.trans' (by norm_num)
        exact_mod_cast this
      have hlogp : Real.log p ≤ Real.log n := by
        refine Real.log_le_log (by linarith) ?_
        exact_mod_cast hpn
      have hq1 : 1 ≤ n / p := Nat.one_le_div_iff hpr.pos |>.2 hpn
      have hinner := norm_convolution_prime_support_le_const hB hb hbB hc hq1
      have hdvd : (n / p) ∣ n := Nat.div_dvd_of_dvd hp.1
      have hωle : ((n / p).primeFactors.card : ℝ) ≤ (n.primeFactors.card : ℝ) := by
        have := Finset.card_le_card (Nat.primeFactors_mono hdvd hn0)
        exact_mod_cast this
      have hlogle : Real.log ((n / p : ℕ) : ℝ) ≤ Real.log n := by
        refine Real.log_le_log ?_ ?_
        · have : (1 : ℕ) ≤ n / p := hq1
          have h1 : (1 : ℝ) ≤ ((n / p : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        · have : (n / p : ℕ) ≤ n := Nat.div_le_self n p
          exact_mod_cast this
      have hinner' : ‖(LSeries.convolution b c) (n / p)‖
          ≤ B * ((n.primeFactors.card : ℝ) * Real.log n) := by
        refine hinner.trans ?_
        have hlognn : (0 : ℝ) ≤ Real.log ((n / p : ℕ) : ℝ) := by
          have h1 : (1 : ℝ) ≤ ((n / p : ℕ) : ℝ) := by exact_mod_cast hq1
          exact Real.log_nonneg h1
        refine mul_le_mul_of_nonneg_left ?_ hB
        calc ((n / p).primeFactors.card : ℝ) * Real.log ((n / p : ℕ) : ℝ)
            ≤ (n.primeFactors.card : ℝ) * Real.log ((n / p : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right hωle hlognn
          _ ≤ (n.primeFactors.card : ℝ) * Real.log n :=
              mul_le_mul_of_nonneg_left hlogle hωnn
      calc ‖a p‖ * ‖(LSeries.convolution b c) (n / p)‖
          ≤ (A * Real.log n) * (B * ((n.primeFactors.card : ℝ) * Real.log n)) := by
            refine mul_le_mul ((haB p).trans (mul_le_mul_of_nonneg_left hlogp hA)) hinner'
              (norm_nonneg _) (mul_nonneg hA hlogn)
        _ = A * B * ((n.primeFactors.card : ℝ) * Real.log n * Real.log n) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, Finset.sum_const, filter_prime_divisors_eq_primeFactors hn0,
    nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- The unit-constant case: `‖(a ⍟ (b ⍟ c))(n)‖ ≤ ω(n)²·(log n)²`. -/
theorem norm_convolution_triple_prime_support_le {a b c : ℕ → ℂ}
    (ha : ∀ p : ℕ, a p ≠ 0 → Nat.Prime p) (haB : ∀ p : ℕ, ‖a p‖ ≤ Real.log p)
    (hb : ∀ q : ℕ, b q ≠ 0 → Nat.Prime q) (hbB : ∀ q : ℕ, ‖b q‖ ≤ Real.log q)
    (hc : ∀ k : ℕ, ‖c k‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖(LSeries.convolution a (LSeries.convolution b c)) n‖
      ≤ (n.primeFactors.card : ℝ) ^ (2 : ℕ) * (Real.log n) ^ (2 : ℕ) := by
  simpa using norm_convolution_triple_prime_support_le_const (A := 1) (B := 1)
    zero_le_one zero_le_one ha (by simpa using haB) hb (by simpa using hbB) hc hn

/-- **`2^ω(n) ≤ n`.**  The product of the distinct prime divisors divides `n`, and each factor is at
least `2`. -/
theorem two_pow_card_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  classical
  have hprod : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have hle : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod' fun p hp => ?_
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  exact le_trans hle (Nat.le_of_dvd (by omega) hprod)

/-- **`ω(n) log 2 ≤ log n`.** -/
theorem card_primeFactors_mul_log_two_le_log {n : ℕ} (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  have h := two_pow_card_primeFactors_le hn
  have hR : ((2 : ℝ) ^ n.primeFactors.card) ≤ (n : ℝ) := by
    have : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    simpa using this
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hlog := Real.log_le_log hpos hR
  rwa [Real.log_pow] at hlog

/-- **The triple convolution's coefficients are polylogarithmic, with constants.**  For prime-supported
`a, b` with `‖a_p‖ ≤ A log p`, `‖b_q‖ ≤ B log q` and `‖c‖ ≤ 1`,

`‖(a ⍟ (b ⍟ c))(n)‖ ≤ A·B·(log n)⁴/(log 2)²`. -/
theorem norm_convolution_triple_le_log_pow_const {a b c : ℕ → ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ p : ℕ, a p ≠ 0 → Nat.Prime p) (haB : ∀ p : ℕ, ‖a p‖ ≤ A * Real.log p)
    (hb : ∀ q : ℕ, b q ≠ 0 → Nat.Prime q) (hbB : ∀ q : ℕ, ‖b q‖ ≤ B * Real.log q)
    (hc : ∀ k : ℕ, ‖c k‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖(LSeries.convolution a (LSeries.convolution b c)) n‖
      ≤ A * B * ((Real.log n) ^ (4 : ℕ) / (Real.log 2) ^ (2 : ℕ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  have hωle : (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact card_primeFactors_mul_log_two_le_log hn
  refine (norm_convolution_triple_prime_support_le_const hA hB ha haB hb hbB hc hn).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA hB)
  have hsq : (n.primeFactors.card : ℝ) ^ (2 : ℕ) ≤ (Real.log n / Real.log 2) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hωle 2
  calc (n.primeFactors.card : ℝ) ^ (2 : ℕ) * (Real.log n) ^ (2 : ℕ)
      ≤ (Real.log n / Real.log 2) ^ (2 : ℕ) * (Real.log n) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (Real.log n) ^ (4 : ℕ) / (Real.log 2) ^ (2 : ℕ) := by
        field_simp

/-- **The triple convolution's coefficients are polylogarithmic, explicitly.**  For prime-supported
`a, b` with `‖a_p‖ ≤ log p`, `‖b_q‖ ≤ log q` and `‖c‖ ≤ 1`,

`‖(a ⍟ (b ⍟ c))(n)‖ ≤ (log n)⁴/(log 2)²`. -/
theorem norm_convolution_triple_le_log_pow {a b c : ℕ → ℂ}
    (ha : ∀ p : ℕ, a p ≠ 0 → Nat.Prime p) (haB : ∀ p : ℕ, ‖a p‖ ≤ Real.log p)
    (hb : ∀ q : ℕ, b q ≠ 0 → Nat.Prime q) (hbB : ∀ q : ℕ, ‖b q‖ ≤ Real.log q)
    (hc : ∀ k : ℕ, ‖c k‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖(LSeries.convolution a (LSeries.convolution b c)) n‖
      ≤ (Real.log n) ^ (4 : ℕ) / (Real.log 2) ^ (2 : ℕ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  have hω := card_primeFactors_mul_log_two_le_log hn
  have hωle : (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact hω
  have hbase := norm_convolution_triple_prime_support_le ha haB hb hbB hc hn
  refine hbase.trans ?_
  have hsq : (n.primeFactors.card : ℝ) ^ (2 : ℕ) ≤ (Real.log n / Real.log 2) ^ (2 : ℕ) := by
    have hnn : (0 : ℝ) ≤ (n.primeFactors.card : ℝ) := Nat.cast_nonneg _
    exact pow_le_pow_left₀ hnn hωle 2
  calc (n.primeFactors.card : ℝ) ^ (2 : ℕ) * (Real.log n) ^ (2 : ℕ)
      ≤ (Real.log n / Real.log 2) ^ (2 : ℕ) * (Real.log n) ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (Real.log n) ^ (4 : ℕ) / (Real.log 2) ^ (2 : ℕ) := by
        field_simp

end RHTower.Sieve
end
