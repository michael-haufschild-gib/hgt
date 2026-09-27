import GaloisForLFunctions.RHTower.XiMassAdjacentPrimeMask
import Mathlib.Analysis.PSeries

/-!
# Cofinal prime gaps below every square-root scale

Euler divergence rules out a positive eventual lower bound on consecutive
square-root prime increments: such a bound would force quadratic growth of
the primes and summability of their reciprocals. Bertrand's theorem transfers
this to additive prime gaps divided by the square root of the lower prime.
These are cofinal existence statements, not bounds on every prime gap.
-/

noncomputable section

namespace RHTower

/-- Arbitrarily late consecutive square-root primes have arbitrarily small gaps. -/
theorem exists_nthPrime_sqrt_gap_lt {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      Real.sqrt (nthPrimeSubtype (n + 1) : ℝ) -
        Real.sqrt (nthPrimeSubtype n : ℝ) < ε := by
  by_contra h
  push Not at h
  have hgrowth (k : ℕ) :
      (k : ℝ) * ε ≤ Real.sqrt (nthPrimeSubtype (N + k) : ℝ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := h (N + k) (by omega)
      rw [Nat.cast_succ, Nat.add_succ]
      nlinarith only [ih, hstep]
  have hs : Summable (fun k : ℕ =>
      (1 / ε ^ 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) :=
    ((summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))).mul_left _
  have htail : Summable (fun k : ℕ => 1 / (nthPrimeSubtype (k + (N + 1)) : ℝ)) := by
    apply hs.of_nonneg_of_le (fun k => by positivity)
    intro k
    have hg := hgrowth (k + 1)
    have hp := nthPrimeSubtype_pos (N + (k + 1))
    have hsq := Real.sq_sqrt hp.le
    have hbound : ε ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 ≤
        (nthPrimeSubtype (N + (k + 1)) : ℝ) := by
      nlinarith [sq_le_sq₀ (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ) * ε)
        (Real.sqrt_nonneg _) |>.2 hg]
    have hden : 0 < ε ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hinv := one_div_le_one_div_of_le hden hbound
    have hindex : k + (N + 1) = N + (k + 1) := by omega
    rw [hindex, one_div_mul_one_div]
    exact hinv
  exact not_summable_nthPrime_reciprocal ((summable_nat_add_iff (N + 1)).1 htail)

/-- Bertrand controls the conversion from square-root increments to normalized gaps. -/
theorem nthPrime_gap_div_sqrt_le_three_sqrt_gap (n : ℕ) :
    ((nthPrimeSubtype (n + 1) : ℝ) - (nthPrimeSubtype n : ℝ)) /
        Real.sqrt (nthPrimeSubtype n : ℝ) ≤
      3 * (Real.sqrt (nthPrimeSubtype (n + 1) : ℝ) -
        Real.sqrt (nthPrimeSubtype n : ℝ)) := by
  let p : ℝ := nthPrimeSubtype n
  let q : ℝ := nthPrimeSubtype (n + 1)
  have hp : 0 < p := nthPrimeSubtype_pos n
  have hq : 0 < q := nthPrimeSubtype_pos (n + 1)
  have hpq : p ≤ q := by
    dsimp only [p, q]
    exact_mod_cast (nthPrimeSubtype_strictMono n.lt_succ_self).le
  have hq2 : q ≤ 2 * p := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_succ_le_two_mul n
  have hsp := Real.sq_sqrt hp.le
  have hsq := Real.sq_sqrt hq.le
  have hs : Real.sqrt q ≤ 2 * Real.sqrt p := by
    nlinarith [Real.sqrt_nonneg p, Real.sqrt_nonneg q]
  have hd : 0 ≤ Real.sqrt q - Real.sqrt p := sub_nonneg.mpr (Real.sqrt_le_sqrt hpq)
  change (q - p) / Real.sqrt p ≤ 3 * (Real.sqrt q - Real.sqrt p)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).2
  nlinarith only [mul_nonneg hd (sub_nonneg.mpr hs), hsp, hsq]

/-- No fixed positive multiple of `sqrt p` eventually bounds all prime gaps below. -/
theorem exists_nthPrime_gap_div_sqrt_lt {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      ((nthPrimeSubtype (n + 1) : ℝ) - (nthPrimeSubtype n : ℝ)) /
        Real.sqrt (nthPrimeSubtype n : ℝ) < ε := by
  obtain ⟨n, hn, hg⟩ := exists_nthPrime_sqrt_gap_lt (div_pos hε (by positivity : (0 : ℝ) < 3)) N
  refine ⟨n, hn, ?_⟩
  have hbound := nthPrime_gap_div_sqrt_le_three_sqrt_gap n
  linarith

end RHTower
