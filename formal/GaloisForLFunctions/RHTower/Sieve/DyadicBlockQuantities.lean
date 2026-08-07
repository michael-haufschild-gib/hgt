import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition
import GaloisForLFunctions.RHTower.Sieve.Mertens
import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# The three quantities of a dyadic block

On the block `2^j ≤ n < 2^{j+1}` the three quantities the sieve mean square consumes are all explicit:

* the coefficients are uniformly bounded — a logarithmic bound `‖a_n‖ ≤ A log n` becomes the constant
  `A(j+1) log 2`;
* the damping is at least its value at the left endpoint, `n^{−c} ≤ 2^{−cj}`;
* the primes of the block number at most `2^{j+1} log 4/(j log 2)`, Chebyshev's `θ` divided by the least
  logarithm in the block — the block's length over its logarithm, which is the saving the sieve is supposed
  to produce and here comes for free.

Together these turn a block's sieve mean square into a product of powers of `2^j` and polynomials in `j`,
which is what makes the block sum a geometric-type series.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **A block's coefficients are uniformly bounded.**  On the block `2^j ≤ n < 2^{j+1}` a logarithmic bound
becomes the constant bound `A(j+1)log 2`. -/
theorem norm_coeffBlock_le_block_bound {a : ℕ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (haB : ∀ n : ℕ, ‖a n‖ ≤ A * Real.log n) (j n : ℕ) :
    ‖coeffBlock a (fun m => Nat.log 2 m) j n‖ ≤ A * (((j : ℝ) + 1) * Real.log 2) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [coeffBlock]
  by_cases hk : Nat.log 2 n = j
  · rw [if_pos hk]
    have hhigh : n < 2 ^ (j + 1) := by
      rw [← hk]
      exact Nat.lt_pow_succ_log_self (by norm_num) n
    have hupper : Real.log (n : ℝ) ≤ ((j : ℝ) + 1) * Real.log 2 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [Nat.cast_zero, Real.log_zero]
        positivity
      · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hhR : (n : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
          have : ((n : ℕ) : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hhigh.le
          simpa using this
        have hlg := Real.log_le_log hnR hhR
        rw [Real.log_pow] at hlg
        calc Real.log (n : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * Real.log 2 := hlg
          _ = ((j : ℝ) + 1) * Real.log 2 := by push_cast; ring
    exact (haB n).trans (mul_le_mul_of_nonneg_left hupper hA)
  · rw [if_neg hk, norm_zero]
    positivity

/-- On the block the damping is at least the damping at the block's left endpoint. -/
theorem rpow_neg_le_block_rpow {n j : ℕ} (hn : 2 ^ j ≤ n) {c : ℝ} (hc : 0 ≤ c) :
    (n : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-(c * (j : ℝ))) := by
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (j : ℕ) := by positivity
  have hnR : ((2 : ℝ) ^ (j : ℕ)) ≤ (n : ℝ) := by
    have : ((2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simpa using this
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hpowpos hnR
  have hbase : ((2 : ℝ) ^ (j : ℝ)) ^ c ≤ (n : ℝ) ^ c := by
    refine Real.rpow_le_rpow (by positivity) ?_ hc
    rw [Real.rpow_natCast]
    exact hnR
  have hinv : ((n : ℝ) ^ c)⁻¹ ≤ (((2 : ℝ) ^ (j : ℝ)) ^ c)⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos (by positivity) c) hbase
  rw [Real.rpow_neg hnpos.le]
  refine hinv.trans (le_of_eq ?_)
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  congr 1
  ring

/-- **The number of primes in a dyadic block.**  Chebyshev's `θ` divided by the least logarithm in the
block: at most `2^{j+1} log 4/(j log 2)` primes, which is the block's length divided by its logarithm. -/
theorem card_prime_block_le {M j : ℕ} (hj : 1 ≤ j) :
    ((#{p ∈ Finset.Icc 1 M | Nat.Prime p ∧ Nat.log 2 p = j} : ℕ) : ℝ)
      ≤ ((2 ^ (j + 1) : ℕ) : ℝ) * Real.log 4 / ((j : ℝ) * Real.log 2) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hden : (0 : ℝ) < (j : ℝ) * Real.log 2 := by positivity
  -- every prime of the block has logarithm at least `j log 2`
  have hlow : ∀ p ∈ Finset.filter (fun p => Nat.Prime p ∧ Nat.log 2 p = j) (Finset.Icc 1 M),
      (j : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, _⟩, _, hlogj⟩ := hp
    have hlowp : (2 : ℕ) ^ j ≤ p := by
      rw [← hlogj]
      exact Nat.pow_log_le_self 2 (by omega)
    have hR : ((2 : ℝ) ^ (j : ℕ)) ≤ (p : ℝ) := by
      have : ((2 ^ j : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlowp
      simpa using this
    have hlg := Real.log_le_log (by positivity) hR
    rwa [Real.log_pow] at hlg
  -- the sum of the logarithms over the block is at most Chebyshev's bound
  have hsub : Finset.filter (fun p => Nat.Prime p ∧ Nat.log 2 p = j) (Finset.Icc 1 M)
      ⊆ Nat.primesLE (2 ^ (j + 1)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, _⟩, hprime, hlogj⟩ := hp
    have hhigh : p < 2 ^ (j + 1) := by
      rw [← hlogj]
      exact Nat.lt_pow_succ_log_self (by norm_num) p
    exact Nat.mem_primesLE.2 ⟨hhigh.le, hprime⟩
  have hnn : ∀ p ∈ Nat.primesLE (2 ^ (j + 1)),
      p ∉ Finset.filter (fun p => Nat.Prime p ∧ Nat.log 2 p = j) (Finset.Icc 1 M) →
      0 ≤ Real.log (p : ℝ) := by
    intro p hp _
    have hprime : p.Prime := Nat.prime_of_mem_primesLE hp
    have h1 : (1 : ℝ) ≤ (p : ℝ) := by
      have := hprime.two_le
      exact_mod_cast this.trans' (by norm_num)
    exact Real.log_nonneg h1
  have hθ : (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ Nat.log 2 p = j) (Finset.Icc 1 M),
        Real.log (p : ℝ))
      ≤ ((2 ^ (j + 1) : ℕ) : ℝ) * Real.log 4 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn)
      (sum_log_primesLE_le (2 ^ (j + 1)))
  have hcard : ((#{p ∈ Finset.Icc 1 M | Nat.Prime p ∧ Nat.log 2 p = j} : ℕ) : ℝ)
      * ((j : ℝ) * Real.log 2)
      ≤ ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ Nat.log 2 p = j) (Finset.Icc 1 M),
          Real.log (p : ℝ) := by
    have h := Finset.sum_le_sum hlow
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  rw [le_div_iff₀ hden]
  linarith [hcard, hθ]

end RHTower.Sieve
end
