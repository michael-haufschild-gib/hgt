import GaloisForLFunctions.RHTower.Sieve.Mertens
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.PSeries
import GaloisForLFunctions.HTGeometry.LogBelowLinear

/-!
# Mertens' first theorem

The weighted prime reciprocal sum satisfies

`∑_{p ≤ n} (log p)/p = log n + O(1)`,

with both constants explicit.  The proof compares Legendre's formula for the exponent of `p` in
`n!` with the elementary factorial bounds `n^n e^{-n} ≤ n! ≤ n^n`:

* the first Legendre term `⌊n/p⌋` alone gives `n ∑ (log p)/p ≤ log n! + ∑_{p ≤ n} log p`, and
  Chebyshev's bound turns the second sum into `n log 4`;
* the full Legendre exponent is at most `n/(p-1)`, and `1/(p-1) = 1/p + 1/(p(p-1))`, so the
  higher prime powers cost only the convergent sum `∑_p (log p)/(p(p-1))`.

No Stirling expansion is needed: only `n^n e^{-n} ≤ n! ≤ n^n`, which follows from a single term of
the exponential series.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The first Legendre term is a lower bound for the exponent of `p` in `n!`. -/
theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n !).factorization p := by
  rcases Nat.lt_or_ge n p with hlt | hge
  · simp [Nat.div_eq_of_lt hlt]
  · have hlog : 1 ≤ Nat.log p n := (Nat.le_log_of_pow_le hp.one_lt (by simpa using hge))
    rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p n))]
    have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n + 1) := by
      simp only [Finset.mem_Ico]
      omega
    have := Finset.single_le_sum (f := fun i => n / p ^ i)
      (fun i _ => Nat.zero_le _) hmem
    simpa using this

/-- `log k ≤ 2 √k`, the comparison making `∑ (log k)/k²` convergent. -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x :=
  GaloisForLFunctions.HTGeometry.log_le_two_mul_sqrt hx

/-- `∑ (log k)/k²` converges. -/
theorem summable_log_div_sq : Summable (fun k : ℕ => Real.log k / (k : ℝ) ^ 2) := by
  have hmaj : Summable (fun k : ℕ => 2 * (1 / (k : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.2 (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le ?_ ?_ hmaj
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : 0 ≤ Real.log k := Real.log_nonneg hk1
      positivity
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hsqrt : Real.log k ≤ 2 * Real.sqrt k := log_le_two_mul_sqrt hk0
      have hrpow : (k : ℝ) ^ ((3 : ℝ) / 2) = (k : ℝ) ^ 2 / Real.sqrt k := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (k : ℝ) 2, ← Real.rpow_sub hk0]
        norm_num
      have hsq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      have hsqrtpos : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 hk0
      rw [hrpow]
      rw [div_le_iff₀ hsq]
      have hexp : 2 * (1 / ((k : ℝ) ^ 2 / Real.sqrt k)) * (k : ℝ) ^ 2
          = 2 * Real.sqrt k := by
        field_simp
      rw [hexp]
      exact hsqrt

/-- The convergent tail constant controlling the higher prime powers in Legendre's formula. -/
noncomputable def logSqTailConst : ℝ := ∑' k : ℕ, Real.log k / (k : ℝ) ^ 2

theorem logSqTailConst_nonneg : 0 ≤ logSqTailConst := by
  refine tsum_nonneg ?_
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : 0 ≤ Real.log k := Real.log_nonneg hk1
    positivity

/-- The higher-prime-power correction in Legendre's formula is uniformly bounded. -/
theorem sum_log_div_prime_mul_pred_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 * logSqTailConst := by
  have hstep : ∀ p ∈ Nat.primesLE n,
      Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 * (Real.log p / (p : ℝ) ^ 2) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesLE hp).two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hden : (p : ℝ) ^ 2 ≤ 2 * ((p : ℝ) * ((p : ℝ) - 1)) := by nlinarith
    have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    rw [div_le_iff₀ hpos]
    have hpp : (0 : ℝ) < (p : ℝ) := by linarith
    have hexp : 2 * (Real.log p / (p : ℝ) ^ 2) * ((p : ℝ) * ((p : ℝ) - 1))
        = Real.log p * (2 * ((p : ℝ) - 1) / (p : ℝ)) := by
      field_simp
    rw [hexp]
    have hfrac : (1 : ℝ) ≤ 2 * ((p : ℝ) - 1) / (p : ℝ) := by
      rw [le_div_iff₀ hpp]
      linarith
    nlinarith [hlog, hfrac]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hsub : Nat.primesLE n ⊆ Finset.range (n + 1) := by
    intro p hp
    have := (Nat.mem_primesLE.1 hp).1
    simp only [Finset.mem_range]
    omega
  have hnonneg : ∀ k : ℕ, 0 ≤ Real.log k / (k : ℝ) ^ 2 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : 0 ≤ Real.log k := Real.log_nonneg hk1
      positivity
  have h1 : ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ^ 2
      ≤ ∑ k ∈ Finset.range (n + 1), Real.log k / (k : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hnonneg k
  have h2 : ∑ k ∈ Finset.range (n + 1), Real.log k / (k : ℝ) ^ 2 ≤ logSqTailConst :=
    summable_log_div_sq.sum_le_tsum _ (fun k _ => hnonneg k)
  linarith

/-- The logarithm of a factorial expanded over the primes up to `n`. -/
theorem log_factorial_eq_sum_primesLE (n : ℕ) :
    Real.log ((n ! : ℕ) : ℝ)
      = ∑ p ∈ Nat.primesLE n, ((n !).factorization p : ℝ) * Real.log p := by
  classical
  have hne : (n ! : ℕ) ≠ 0 := Nat.factorial_ne_zero n
  have hprodN : (n ! : ℕ) = ∏ p ∈ (n !).primeFactors, p ^ ((n !).factorization p) := by
    have h := Nat.prod_factorization_pow_eq_self hne
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact h.symm
  have hprodR : ((n ! : ℕ) : ℝ)
      = ∏ p ∈ (n !).primeFactors, ((p : ℝ) ^ ((n !).factorization p)) := by
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hprodN
    push_cast at hcast
    exact hcast
  have hlog : Real.log ((n ! : ℕ) : ℝ)
      = ∑ p ∈ (n !).primeFactors, ((n !).factorization p : ℝ) * Real.log p := by
    rw [hprodR, Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro p _
      rw [Real.log_pow]
    · intro p hp
      have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
      positivity
  rw [hlog]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact Nat.mem_primesLE.2 ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _ hnot
    have : (n !).factorization p = 0 := by
      by_contra hcon
      exact hnot (Nat.support_factorization (n !) ▸ Finsupp.mem_support_iff.2 hcon)
    simp [this]

/-- `n! ≤ n^n`, in logarithmic form. -/
theorem log_factorial_le (n : ℕ) : Real.log ((n ! : ℕ) : ℝ) ≤ (n : ℝ) * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hfacpos : (0 : ℝ) < ((n ! : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    have hle : ((n ! : ℕ) : ℝ) ≤ ((n : ℝ)) ^ n := by
      exact_mod_cast Nat.factorial_le_pow n
    calc Real.log ((n ! : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log hfacpos hle
      _ = (n : ℝ) * Real.log n := by rw [Real.log_pow]

/-- `n^n e^{-n} ≤ n!`, in logarithmic form.  The proof uses one term of the exponential series. -/
theorem le_log_factorial (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log ((n ! : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hfacpos : (0 : ℝ) < ((n ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hsum := Real.sum_le_exp_of_nonneg (x := (n : ℝ)) hn0.le (n + 1)
    have hterm : (n : ℝ) ^ n / ((n ! : ℕ) : ℝ)
        ≤ ∑ i ∈ Finset.range (n + 1), (n : ℝ) ^ i / ((i ! : ℕ) : ℝ) := by
      refine Finset.single_le_sum (f := fun i => (n : ℝ) ^ i / ((i ! : ℕ) : ℝ)) ?_ ?_
      · intro i _
        have : (0 : ℝ) < ((i ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos i
        positivity
      · simp
    have hquot : (n : ℝ) ^ n / ((n ! : ℕ) : ℝ) ≤ Real.exp n := le_trans hterm hsum
    have hqpos : (0 : ℝ) < (n : ℝ) ^ n / ((n ! : ℕ) : ℝ) := by positivity
    have hlog : Real.log ((n : ℝ) ^ n / ((n ! : ℕ) : ℝ)) ≤ (n : ℝ) := by
      calc Real.log ((n : ℝ) ^ n / ((n ! : ℕ) : ℝ))
          ≤ Real.log (Real.exp n) := Real.log_le_log hqpos hquot
        _ = (n : ℝ) := Real.log_exp _
    rw [Real.log_div (by positivity) (ne_of_gt hfacpos), Real.log_pow] at hlog
    linarith

/-- **Mertens' first theorem, upper bound.** -/
theorem mertensFirst_upper {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlower : ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
      ≤ Real.log ((n ! : ℕ) : ℝ) := by
    rw [log_factorial_eq_sum_primesLE n]
    refine Finset.sum_le_sum ?_
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    have hle : ((n / p : ℕ) : ℝ) ≤ (((n !).factorization p : ℕ) : ℝ) := by
      exact_mod_cast div_le_factorization_factorial hprime n
    exact mul_le_mul_of_nonneg_right hle hlogp
  have hfloor : (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ))
      - ∑ p ∈ Nat.primesLE n, Real.log p
      ≤ ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum ?_
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hppos : 0 < p := hprime.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    have hbound := (cast_div_bounds (d := p) (n := n) hppos).2
    have hfl : (n : ℝ) / (p : ℝ) - 1 ≤ ((n / p : ℕ) : ℝ) := by linarith
    have : (n : ℝ) * (Real.log p / (p : ℝ)) - Real.log p
        = ((n : ℝ) / (p : ℝ) - 1) * Real.log p := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hfl hlogp
  have hcheb := sum_log_primesLE_le n
  have hfac := log_factorial_le n
  have hkey : (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ))
      ≤ (n : ℝ) * Real.log n + (n : ℝ) * Real.log 4 := by linarith
  refine le_of_mul_le_mul_left ?_ hn0
  have hring : (n : ℝ) * (Real.log n + Real.log 4)
      = (n : ℝ) * Real.log n + (n : ℝ) * Real.log 4 := by ring
  rw [hring]
  exact hkey

/-- **Mertens' first theorem, lower bound.** -/
theorem mertensFirst_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.log n - 1 - 2 * logSqTailConst
      ≤ ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper : Real.log ((n ! : ℕ) : ℝ)
      ≤ ∑ p ∈ Nat.primesLE n, ((n : ℝ) / ((p : ℝ) - 1)) * Real.log p := by
    rw [log_factorial_eq_sum_primesLE n]
    refine Finset.sum_le_sum ?_
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : 2 ≤ p := hprime.two_le
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    have hle : (((n !).factorization p : ℕ) : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hprime n
    have hpred : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      have hpos : 0 < p - 1 := by omega
      have := (cast_div_bounds (d := p - 1) (n := n) hpos).1
      have hcast : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
        have : (1 : ℕ) ≤ p := by omega
        push_cast [Nat.cast_sub this]
        ring
      rwa [hcast] at this
    exact mul_le_mul_of_nonneg_right (le_trans hle hpred) hlogp
  have hsplit : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / ((p : ℝ) - 1)) * Real.log p
      = (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ))
        + (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      intro hcon
      linarith [hcon]
    field_simp
    ring
  have htail := sum_log_div_prime_mul_pred_le n
  have hfac := le_log_factorial n
  have hkey : (n : ℝ) * Real.log n - (n : ℝ)
      ≤ (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ))
        + (n : ℝ) * (2 * logSqTailConst) := by
    have h1 : (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤ (n : ℝ) * (2 * logSqTailConst) :=
      mul_le_mul_of_nonneg_left htail hn0.le
    rw [hsplit] at hupper
    linarith
  refine le_of_mul_le_mul_left ?_ hn0
  have hring : (n : ℝ) * (Real.log n - 1 - 2 * logSqTailConst)
      = (n : ℝ) * Real.log n - (n : ℝ) - (n : ℝ) * (2 * logSqTailConst) := by ring
  rw [hring]
  linarith

end RHTower.Sieve
