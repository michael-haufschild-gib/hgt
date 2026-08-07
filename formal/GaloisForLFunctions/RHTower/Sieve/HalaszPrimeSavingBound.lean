import GaloisForLFunctions.RHTower.Sieve.HalaszExplicitParameters
import GaloisForLFunctions.RHTower.Sieve.PrimeLogSqZetaCap
/-!
# The master bound with the prime saving kept

For prime-supported coefficients the mean-square majorant only sees the primes, so the index set of the
split may be cut down to them at no cost, and each of the two sums is then bounded by the dyadic Chebyshev
cap rather than by the integer cap:

`sieveBoundPrime A σ z Y = (4 sinh δ/log Y)·A²·cap(2σ−1) + (2/log Y + E + z)·A²·cap(2σ)`,
`cap(w) = 2 log 2 log 4 ((1−2^{1−w})⁻¹ + 2^{1−w}/(1−2^{1−w})²)`.

Each cap is smaller than its integer counterpart by a factor `1/(w−1)`, so at `σ = 1 + 1/log N` the linear
term is `(log N)²` where it was `(log N)³`.  The master bound holds verbatim with these caps in place of the
integer ones.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- For prime-supported coefficients the mean-square majorant only sees the primes. -/
theorem sieveMeanSquare_eq_filter_prime {a : ℕ → ℂ}
    (hprime : ∀ n : ℕ, a n ≠ 0 → Nat.Prime n) (s : Finset ℕ) (σ : ℝ) (z Y : ℕ) :
    sieveMeanSquare a s σ z Y
      = sieveMeanSquare a (Finset.filter (fun n => Nat.Prime n) s) σ z Y := by
  classical
  rw [sieveMeanSquare, sieveMeanSquare]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun n hn hnot => ?_).symm
  have hz : a n = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.2 ⟨hn, hprime n hne⟩)
  rw [hz, zero_mul, norm_zero]
  simp

/-- The dyadic Chebyshev cap of the sieve majorant, at the exponent `w`. -/
def sieveCapPrime (w : ℝ) : ℝ :=
  2 * Real.log 2 * Real.log 4
    * ((1 - (2 : ℝ) ^ (1 - w))⁻¹ + (2 : ℝ) ^ (1 - w) / (1 - (2 : ℝ) ^ (1 - w)) ^ 2)

/-- The explicit majorant of the sieve mean square of a **prime-supported** weight with
`‖a_n‖ ≤ A log n`: the two dyadic Chebyshev caps in place of the integer caps. -/
def sieveBoundPrime (A σ : ℝ) (z Y : ℕ) : ℝ :=
  (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) / Real.log Y)
      * (A ^ 2 * sieveCapPrime (2 * σ - 1))
    + (2 / Real.log Y + selbergFibreError z Y + (z : ℝ)) * (A ^ 2 * sieveCapPrime (2 * σ))

/-- **The sieve mean square of a prime-supported weight, with the prime saving kept.**  The index set is
first cut down to the primes — free, since the coefficients vanish elsewhere — and then the dyadic Chebyshev
cap is applied to each of the two sums of the split. -/
theorem sieveMeanSquare_le_sieveBoundPrime {a : ℕ → ℂ} {A : ℝ}
    (haB : ∀ n : ℕ, ‖a n‖ ≤ A * Real.log n) (hprime : ∀ n : ℕ, a n ≠ 0 → Nat.Prime n)
    (M : ℕ) {σ : ℝ} (hσ : 1 < σ) (z Y : ℕ) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    sieveMeanSquare a (Finset.Icc 1 M) σ z Y ≤ sieveBoundPrime A σ z Y := by
  classical
  have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  have hS0 : 0 ≤ 2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi))))
      / Real.log Y := by
    have h := Real.exp_le_exp.2 (show -(1 / (2 * Real.pi)) ≤ 1 / (2 * Real.pi) by linarith)
    exact div_nonneg (by linarith) hlogY.le
  have herr : 0 ≤ selbergFibreError z Y := selbergFibreError_nonneg hz Y
  have hc2 : (0 : ℝ) ≤ 2 / Real.log Y + selbergFibreError z Y + (z : ℝ) := by
    have h1 : (0 : ℝ) ≤ 2 / Real.log Y := by positivity
    have hzR : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
    linarith
  have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  rw [sieveMeanSquare_eq_filter_prime hprime]
  refine le_trans (sieveMeanSquare_le_of_norm_le_log haB
    (Finset.filter (fun n => Nat.Prime n) (Finset.Icc 1 M))
    (fun n hn => (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1) σ z Y hz hlogY) ?_
  rw [sieveBoundPrime]
  -- the linear sum, at `w = 2σ − 1`
  have hw1 : (1 : ℝ) < 2 * σ - 1 := by linarith
  have hlin : (∑ n ∈ Finset.filter (fun n => Nat.Prime n) (Finset.Icc 1 M),
        (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
      ≤ sieveCapPrime (2 * σ - 1) := by
    have hrw : (∑ n ∈ Finset.filter (fun n => Nat.Prime n) (Finset.Icc 1 M),
          (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
        = ∑ p ∈ Finset.Icc 1 M with Nat.Prime p,
            (p : ℝ) ^ (-(2 * σ - 1)) * (Real.log p) ^ 2 :=
      Finset.sum_congr rfl fun n _ => by
        congr 2
        ring
    rw [hrw, sieveCapPrime]
    exact sum_prime_logSq_rpow_neg_le hw1 M
  -- the constant sum, at `w = 2σ`
  have hw2 : (1 : ℝ) < 2 * σ := by linarith
  have hcst : (∑ n ∈ Finset.filter (fun n => Nat.Prime n) (Finset.Icc 1 M),
        (n : ℝ) ^ (-(2 * σ)) * (Real.log n) ^ 2)
      ≤ sieveCapPrime (2 * σ) := by
    rw [sieveCapPrime]
    exact sum_prime_logSq_rpow_neg_le hw2 M
  have hstep1 : (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi))))
        / Real.log Y)
        * (A ^ 2 * ∑ n ∈ Finset.filter (fun n => Nat.Prime n) (Finset.Icc 1 M),
            (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
      ≤ (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) / Real.log Y)
        * (A ^ 2 * sieveCapPrime (2 * σ - 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlin hA2) hS0
  have hstep2 : (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
        * (A ^ 2 * ∑ n ∈ Finset.filter (fun n => Nat.Prime n) (Finset.Icc 1 M),
            (n : ℝ) ^ (-(2 * σ)) * (Real.log n) ^ 2)
      ≤ (2 / Real.log Y + selbergFibreError z Y + (z : ℝ)) * (A ^ 2 * sieveCapPrime (2 * σ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcst hA2) hc2
  linarith [hstep1, hstep2]

/-- **The master bound with the prime saving kept.**  The same inequality as before with both sieve mean
squares majorised by their dyadic Chebyshev caps, which are smaller than the integer caps by a factor
`1/(σ−1)`. -/
theorem exists_norm_sum_Icc_mul_log_le_sieveBoundPrime {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
        ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
            + (9 + RHTower.Mertens.mertensTail)
                * ((N : ℝ)
                    * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                          / Real.log 2)
                        * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
          + (H + 1) * ((Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
          + (1 / (2 * Real.pi))
              * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C
                  * (Real.sqrt (25 * Real.pi ^ 2 * sieveBoundPrime (1 / Real.log 2) σ z Y)
                      * Real.sqrt (25 * Real.pi ^ 2 * sieveBoundPrime 1 σ z Y))) := by
  obtain ⟨C, hC0, hmain⟩ :=
    exists_norm_sum_Icc_mul_log_le hf1 hfmul hbdd N hN hH hσ z Y hY hYz hz hlogY
  refine ⟨C, hC0, hmain.trans ?_⟩
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hout := sieveMeanSquare_le_sieveBoundPrime (norm_ghsOuter_le hbdd N)
    (fun n hn => ghsOuter_support hn) N hσ z Y hz hlogY
  have hin := sieveMeanSquare_le_sieveBoundPrime (A := 1)
    (by simpa using norm_ghsInner_le hbdd N) (fun n hn => ghsInner_support hn) N hσ z Y hz hlogY
  have hsq : Real.sqrt (25 * Real.pi ^ 2 * sieveMeanSquare (ghsOuter f N) (Finset.Icc 1 N) σ z Y)
        * Real.sqrt (25 * Real.pi ^ 2 * sieveMeanSquare (ghsInner f N) (Finset.Icc 1 N) σ z Y)
      ≤ Real.sqrt (25 * Real.pi ^ 2 * sieveBoundPrime (1 / Real.log 2) σ z Y)
        * Real.sqrt (25 * Real.pi ^ 2 * sieveBoundPrime 1 σ z Y) := by
    refine mul_le_mul (Real.sqrt_le_sqrt (by nlinarith [hout, sq_nonneg Real.pi, Real.pi_pos]))
      (Real.sqrt_le_sqrt (by nlinarith [hin, sq_nonneg Real.pi, Real.pi_pos]))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmul0 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C) := by
    have h1 : 0 < σ - 1 := by linarith
    have hfac : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by positivity
    have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    exact mul_nonneg hpi.le (mul_nonneg hfac hC0)
  nlinarith [mul_le_mul_of_nonneg_left hsq hmul0]

end RHTower.Sieve
end
