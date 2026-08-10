import GaloisForLFunctions.RHTower.Sieve.PerronKernelCellSum
import GaloisForLFunctions.RHTower.Sieve.GhsCoefficients
import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# The cell mass of the two Granville–Harper–Soundararajan prime weights

The cell mass `primeCellMass c s = (5/4)∑_q (700 q/log q + 1)‖c q‖²` collapses to a single Mertens
sum, because `1 ≤ q/log q` for every prime, so the additive `+1` is absorbed:

```text
primeCellMass c s ≤ (5/4)·701·∑_{q ∈ s} (q/log q)·‖c q‖² .
```

For the two weights of the argument, at any abscissa `σ ≥ 1`, the weighted term is

```text
inner   b_q = f(q)·log q             →  (q/log q)‖b_q q^{-σ}‖² ≤ log q/q
outer   a_p = f(p)·log p/log(N/p)    →  (p/log p)‖a_p p^{-σ}‖² ≤ log p/(p·log²(N/p))
```

Summing the first is Mertens' first theorem, `≤ log M + log 4`.  Summing the second gives the `I₁`
of the argument; the reason it carries `log p` rather than `(log p)²` is the prime near-diagonal
weight `q/log q`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset Complex

/-- For a prime the near-diagonal weight dominates one. -/
theorem one_le_div_log_of_prime {q : ℕ} (hq : q.Prime) : 1 ≤ (q : ℝ) / Real.log q := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
  have hlog : (0 : ℝ) < Real.log q := Real.log_pos (by linarith)
  rw [le_div_iff₀ hlog]
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < (q : ℝ) by linarith)]

/-- **The additive term of the cell mass is absorbed.** -/
theorem primeCellMass_le_weighted (c : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ m ∈ s, m.Prime) :
    primeCellMass c s ≤ (5 / 4) * 701 * ∑ q ∈ s, ((q : ℝ) / Real.log q) * ‖c q‖ ^ 2 := by
  have hterm : ∑ q ∈ s, (700 * ((q : ℝ) / Real.log q) + 1) * ‖c q‖ ^ 2
      ≤ 701 * ∑ q ∈ s, ((q : ℝ) / Real.log q) * ‖c q‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hone := one_le_div_log_of_prime (hs q hq)
    have hsq : (0 : ℝ) ≤ ‖c q‖ ^ 2 := by positivity
    have hcoef : 700 * ((q : ℝ) / Real.log q) + 1 ≤ 701 * ((q : ℝ) / Real.log q) := by linarith
    calc (700 * ((q : ℝ) / Real.log q) + 1) * ‖c q‖ ^ 2
        ≤ (701 * ((q : ℝ) / Real.log q)) * ‖c q‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef hsq
      _ = 701 * (((q : ℝ) / Real.log q) * ‖c q‖ ^ 2) := by ring
  rw [primeCellMass]
  calc (5 / 4 : ℝ) * ∑ q ∈ s, (700 * ((q : ℝ) / Real.log q) + 1) * ‖c q‖ ^ 2
      ≤ (5 / 4 : ℝ) * (701 * ∑ q ∈ s, ((q : ℝ) / Real.log q) * ‖c q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hterm (by norm_num)
    _ = (5 / 4) * 701 * ∑ q ∈ s, ((q : ℝ) / Real.log q) * ‖c q‖ ^ 2 := by ring

/-- The Perron damping is at most the reciprocal past the abscissa one. -/
theorem rpow_neg_le_inv {q : ℕ} (hq2 : (2 : ℝ) ≤ (q : ℝ)) {σ : ℝ} (hσ : 1 ≤ σ) :
    (q : ℝ) ^ (-σ) ≤ 1 / (q : ℝ) := by
  have h1 : (q : ℝ) ^ (-σ) ≤ (q : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (q : ℝ) ^ (-1 : ℝ) = 1 / (q : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  linarith [h1, h2.le, h2.ge]

/-- **The inner weight's term.** -/
theorem ghsInner_weighted_term_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ)
    {M q : ℕ} (hqp : q.Prime) (hqM : q ≤ M) :
    ((q : ℝ) / Real.log q) * ‖ghsInner f M q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ Real.log q / (q : ℝ) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog : (0 : ℝ) < Real.log q := Real.log_pos (by linarith)
  have hval : ghsInner f M q = f q * ((Real.log q : ℝ) : ℂ) := by
    rw [ghsInner, if_pos ⟨hqp, hqM⟩]
  have hnorm : ‖ghsInner f M q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ≤ Real.log q / (q : ℝ) := by
    rw [hval, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hlog, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    have hb := hbdd q
    have hr := rpow_neg_le_inv hq2 hσ
    have hrn : (0 : ℝ) ≤ (q : ℝ) ^ (-σ) := Real.rpow_nonneg hq0.le _
    have hstep : ‖f q‖ * Real.log q * ((q : ℝ) ^ (-σ)) ≤ 1 * Real.log q * (1 / (q : ℝ)) := by
      have h1 : ‖f q‖ * Real.log q ≤ 1 * Real.log q := mul_le_mul_of_nonneg_right hb hlog.le
      have h2 : (0 : ℝ) ≤ ‖f q‖ * Real.log q := mul_nonneg (norm_nonneg _) hlog.le
      nlinarith [h1, h2, hr, hrn, hlog.le]
    calc ‖f q‖ * Real.log q * ((q : ℝ) ^ (-σ)) ≤ 1 * Real.log q * (1 / (q : ℝ)) := hstep
      _ = Real.log q / (q : ℝ) := by ring
  have hnn : (0 : ℝ) ≤ Real.log q / (q : ℝ) := by positivity
  have hsq : ‖ghsInner f M q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ (Real.log q / (q : ℝ)) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖ghsInner f M q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ := norm_nonneg _
    nlinarith [hnorm, h0, hnn]
  have heq : ((q : ℝ) / Real.log q) * (Real.log q / (q : ℝ)) ^ 2 = Real.log q / (q : ℝ) := by
    field_simp
  calc ((q : ℝ) / Real.log q) * ‖ghsInner f M q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ ((q : ℝ) / Real.log q) * (Real.log q / (q : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = Real.log q / (q : ℝ) := heq

/-- **The outer weight's term.** -/
theorem ghsOuter_weighted_term_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ)
    {N p : ℕ} (hpp : p.Prime) :
    ((p : ℝ) / Real.log p) * ‖ghsOuter f N p * ((((p : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ Real.log p / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : (0 : ℝ) < Real.log p := Real.log_pos (by linarith)
  by_cases hcond : Nat.Prime p ∧ 2 ≤ N / p
  · have hq2 : (2 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hcond.2
    have hlq : (0 : ℝ) < Real.log ((N / p : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hval : ghsOuter f N p = f p * ((Real.log p / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [ghsOuter, if_pos hcond]
    have hwpos : (0 : ℝ) < Real.log p / Real.log ((N / p : ℕ) : ℝ) := by positivity
    have hnorm : ‖ghsOuter f N p * ((((p : ℝ) ^ (-σ) : ℝ)) : ℂ)‖
        ≤ (Real.log p / Real.log ((N / p : ℕ) : ℝ)) / (p : ℝ) := by
      rw [hval, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hwpos, abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
      have hb := hbdd p
      have hr := rpow_neg_le_inv hp2 hσ
      have hrn : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
      have h1 : ‖f p‖ * (Real.log p / Real.log ((N / p : ℕ) : ℝ))
          ≤ 1 * (Real.log p / Real.log ((N / p : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hb hwpos.le
      have h2 : (0 : ℝ) ≤ ‖f p‖ * (Real.log p / Real.log ((N / p : ℕ) : ℝ)) :=
        mul_nonneg (norm_nonneg _) hwpos.le
      have hstep : ‖f p‖ * (Real.log p / Real.log ((N / p : ℕ) : ℝ)) * ((p : ℝ) ^ (-σ))
          ≤ 1 * (Real.log p / Real.log ((N / p : ℕ) : ℝ)) * (1 / (p : ℝ)) := by
        nlinarith [h1, h2, hr, hrn, hwpos.le]
      calc ‖f p‖ * (Real.log p / Real.log ((N / p : ℕ) : ℝ)) * ((p : ℝ) ^ (-σ))
          ≤ 1 * (Real.log p / Real.log ((N / p : ℕ) : ℝ)) * (1 / (p : ℝ)) := hstep
        _ = (Real.log p / Real.log ((N / p : ℕ) : ℝ)) / (p : ℝ) := by ring
    have hnn : (0 : ℝ) ≤ (Real.log p / Real.log ((N / p : ℕ) : ℝ)) / (p : ℝ) := by positivity
    have hsq : ‖ghsOuter f N p * ((((p : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        ≤ ((Real.log p / Real.log ((N / p : ℕ) : ℝ)) / (p : ℝ)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖ghsOuter f N p * ((((p : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ := norm_nonneg _
      nlinarith [hnorm, h0, hnn]
    have heq : ((p : ℝ) / Real.log p)
          * ((Real.log p / Real.log ((N / p : ℕ) : ℝ)) / (p : ℝ)) ^ 2
        = Real.log p / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ 2) := by
      field_simp
    calc ((p : ℝ) / Real.log p) * ‖ghsOuter f N p * ((((p : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        ≤ ((p : ℝ) / Real.log p) * ((Real.log p / Real.log ((N / p : ℕ) : ℝ)) / (p : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Real.log p / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ 2) := heq
  · have hzero : ghsOuter f N p = 0 := by rw [ghsOuter, if_neg hcond]
    rw [hzero]
    simp only [zero_mul, norm_zero]
    have hnn : (0 : ℝ) ≤ Real.log p / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ 2) := by positivity
    simpa using hnn

/-- **The inner weight's cell mass is Mertens' first theorem.** -/
theorem primeCellMass_ghsInner_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ)
    (M : ℕ) (hM : 1 ≤ M) :
    primeCellMass (fun n => ghsInner f M n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE M)
      ≤ (5 / 4) * 701 * (Real.log M + Real.log 4) := by
  have hprime : ∀ q ∈ Nat.primesLE M, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
  have hsum : ∑ q ∈ Nat.primesLE M,
        ((q : ℝ) / Real.log q) * ‖ghsInner f M q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ ∑ q ∈ Nat.primesLE M, Real.log q / (q : ℝ) :=
    Finset.sum_le_sum fun q hq =>
      ghsInner_weighted_term_le hbdd hσ (hprime q hq) (Nat.mem_primesLE.1 hq).1
  calc primeCellMass (fun n => ghsInner f M n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE M)
      ≤ (5 / 4) * 701 * ∑ q ∈ Nat.primesLE M,
          ((q : ℝ) / Real.log q) * ‖ghsInner f M q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
        primeCellMass_le_weighted _ hprime
    _ ≤ (5 / 4) * 701 * ∑ q ∈ Nat.primesLE M, Real.log q / (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ (5 / 4) * 701 * (Real.log M + Real.log 4) :=
        mul_le_mul_of_nonneg_left (mertensFirst_upper hM) (by norm_num)

/-- **The outer weight's cell mass is the `I₁` sum of the argument.** -/
theorem primeCellMass_ghsOuter_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ)
    (N : ℕ) :
    primeCellMass (fun n => ghsOuter f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE N)
      ≤ (5 / 4) * 701
          * ∑ p ∈ Nat.primesLE N,
              Real.log p / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ 2) := by
  have hprime : ∀ q ∈ Nat.primesLE N, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
  have hsum : ∑ p ∈ Nat.primesLE N,
        ((p : ℝ) / Real.log p) * ‖ghsOuter f N p * ((((p : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ 2) :=
    Finset.sum_le_sum fun p hp => ghsOuter_weighted_term_le hbdd hσ (hprime p hp)
  calc primeCellMass (fun n => ghsOuter f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) (Nat.primesLE N)
      ≤ (5 / 4) * 701 * ∑ p ∈ Nat.primesLE N,
          ((p : ℝ) / Real.log p) * ‖ghsOuter f N p * ((((p : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
        primeCellMass_le_weighted _ hprime
    _ ≤ (5 / 4) * 701 * ∑ p ∈ Nat.primesLE N,
          Real.log p / ((p : ℝ) * (Real.log ((N / p : ℕ) : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- **The mean square over a range of `m` unit cells.**  The constant envelope of the cell
aggregate: no height enters beyond the number of cells. -/
theorem integral_normSq_LSeries_le_cells {a : ℕ → ℂ} {s : Finset ℕ}
    (hs : ∀ m ∈ s, m.Prime) (hs0 : 0 ∉ s) (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ b : ℝ) (m : ℕ) :
    (∫ y in b..(b + (m : ℝ) * 1), ‖LSeries a ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2)
      ≤ (m : ℝ) * (2 * Real.pi
          * primeCellMass (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s) := by
  obtain ⟨v, -, hle⟩ := exists_cell_aggregate_normSq_LSeries_le hs hs0 hsupp
    (E := fun _ : ℝ => (1 : ℝ)) continuous_const (fun _ => zero_le_one) σ b m
  simpa using hle

end RHTower.Sieve

end
