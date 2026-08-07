import GaloisForLFunctions.RHTower.Sieve.DyadicBlockQuantities
import GaloisForLFunctions.RHTower.Sieve.HalaszExplicitParameters
/-!
# A dyadic block's sieve mean square, in closed form

Substituting the three block quantities into the majorant, a block's sieve mean square is a product of four
explicit factors: the number of primes of the block, the largest value of the Selberg count on it, the block's
uniform coefficient bound squared, and the damping at its left endpoint —

`sieveMeanSquare a_j (Icc 1 M) σ z Y
    ≤ (2^{j+1} log 4/(j log 2))·(2(2^{j+1}·2 sinh δ + 1)/log Y + E + z)·(A(j+1)log 2)²·2^{−2σj}`.

Every factor is a power of `2^j` or a polynomial in `j`, so the sum over the blocks is a geometric-type series
in `j` once a level sequence `(z_j, Y_j)` is fixed.  The level is still free here: nothing in the statement
constrains `Y` beyond admissibility, which is what allows it to be chosen per block.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **A block's sieve mean square, in closed form.**  The three block quantities substituted into the
majorant: the number of primes of the block, the largest value of the Selberg count on it, the block's uniform
coefficient bound, and the damping at its left endpoint. -/
theorem sieveMeanSquare_coeffBlock_le_of_bound {a : ℕ → ℂ} {Bc : ℝ} {j : ℕ}
    (hBc : ∀ n : ℕ, ‖coeffBlock a (fun m => Nat.log 2 m) j n‖ ≤ Bc)
    (hprime : ∀ n : ℕ, a n ≠ 0 → Nat.Prime n)
    (M : ℕ) (hj : 1 ≤ j) {σ : ℝ} (hσ : 0 < σ) (z Y : ℕ) (hz : 2 ≤ z)
    (hlogY : 0 < Real.log Y) :
    sieveMeanSquare (coeffBlock a (fun m => Nat.log 2 m) j) (Finset.Icc 1 M) σ z Y
      ≤ (((2 ^ (j + 1) : ℕ) : ℝ) * Real.log 4 / ((j : ℝ) * Real.log 2))
          * ((2 * (((2 ^ (j + 1) : ℕ) : ℝ)
                  * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
                / Real.log Y + selbergFibreError z Y + (z : ℝ))
              * (Bc ^ 2 * (2 : ℝ) ^ (-(2 * σ * (j : ℝ))))) := by
  classical
  set S : ℝ := Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi))) with hSdef
  have hS0 : 0 ≤ S := by
    have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    have h := Real.exp_le_exp.2 (show -(1 / (2 * Real.pi)) ≤ 1 / (2 * Real.pi) by linarith)
    rw [hSdef]
    linarith
  have herr : 0 ≤ selbergFibreError z Y := selbergFibreError_nonneg hz Y
  have hzR : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  set Kmax : ℝ := 2 * (((2 ^ (j + 1) : ℕ) : ℝ) * S + 1) / Real.log Y
      + selbergFibreError z Y + (z : ℝ) with hK
  set B : ℝ := Bc ^ 2 * (2 : ℝ) ^ (-(2 * σ * (j : ℝ))) with hB
  have hKmax0 : 0 ≤ Kmax := by
    have hnum : (0 : ℝ) ≤ 2 * (((2 ^ (j + 1) : ℕ) : ℝ) * S + 1) := by positivity
    have : (0 : ℝ) ≤ 2 * (((2 ^ (j + 1) : ℕ) : ℝ) * S + 1) / Real.log Y :=
      div_nonneg hnum hlogY.le
    rw [hK]
    linarith
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  -- the sum is carried by the primes of the block
  have hred : sieveMeanSquare (coeffBlock a (fun m => Nat.log 2 m) j) (Finset.Icc 1 M) σ z Y
      = ∑ n ∈ Finset.Icc 1 M with (Nat.Prime n ∧ Nat.log 2 n = j),
          (2 * ((n : ℝ) * S + 1) / Real.log Y + selbergFibreError z Y + (z : ℝ))
            * ‖coeffBlock a (fun m => Nat.log 2 m) j n
                * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := by
    rw [sieveMeanSquare, hSdef]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun n hn hnot => ?_).symm
    have hzero : coeffBlock a (fun m => Nat.log 2 m) j n = 0 := by
      by_cases hk : Nat.log 2 n = j
      · have hane : a n = 0 := by
          by_contra hne
          exact hnot (Finset.mem_filter.2 ⟨hn, hprime n hne, hk⟩)
        rw [coeffBlock, if_pos hk, hane]
      · rw [coeffBlock, if_neg hk]
    rw [hzero, zero_mul, norm_zero]
    simp
  rw [hred]
  have hterm : ∀ n ∈ Finset.filter (fun n => Nat.Prime n ∧ Nat.log 2 n = j) (Finset.Icc 1 M),
      (2 * ((n : ℝ) * S + 1) / Real.log Y + selbergFibreError z Y + (z : ℝ))
          * ‖coeffBlock a (fun m => Nat.log 2 m) j n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        ≤ Kmax * B := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, hnprime, hnlog⟩ := hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    -- the count
    have hhigh : n < 2 ^ (j + 1) := by
      rw [← hnlog]
      exact Nat.lt_pow_succ_log_self (by norm_num) n
    have hhighR : (n : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hhigh.le
    have hKle : 2 * ((n : ℝ) * S + 1) / Real.log Y + selbergFibreError z Y + (z : ℝ) ≤ Kmax := by
      rw [hK]
      have hnum : 2 * ((n : ℝ) * S + 1) ≤ 2 * (((2 ^ (j + 1) : ℕ) : ℝ) * S + 1) := by
        nlinarith [mul_le_mul_of_nonneg_right hhighR hS0]
      have hdiv := div_le_div_of_nonneg_right hnum hlogY.le
      linarith [hdiv]
    -- the coefficient and the damping
    have hcoeff : ‖coeffBlock a (fun m => Nat.log 2 m) j n‖ ≤ Bc := hBc n
    have hlow : (2 : ℕ) ^ j ≤ n := by
      rw [← hnlog]
      exact Nat.pow_log_le_self 2 (by omega)
    have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hnpos.le _
    have hsq : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hnpos.le]
      norm_num
      ring_nf
    have hdamp : (n : ℝ) ^ (-(2 * σ)) ≤ (2 : ℝ) ^ (-(2 * σ * (j : ℝ))) :=
      rpow_neg_le_block_rpow hlow (by positivity)
    have hnormsq : ‖coeffBlock a (fun m => Nat.log 2 m) j n
        * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ B := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrpow, mul_pow, hsq, hB]
      refine mul_le_mul ?_ hdamp (Real.rpow_nonneg hnpos.le _) (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) hcoeff 2
    exact mul_le_mul hKle hnormsq (by positivity) hKmax0
  refine le_trans (Finset.sum_le_card_nsmul _ _ (Kmax * B) hterm) ?_
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hKmax0 hB0)
  exact card_prime_block_le hj

/-- The case of a logarithmic coefficient bound, where the block's uniform bound is `A(j+1)log 2`. -/
theorem sieveMeanSquare_coeffBlock_le {a : ℕ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (haB : ∀ n : ℕ, ‖a n‖ ≤ A * Real.log n) (hprime : ∀ n : ℕ, a n ≠ 0 → Nat.Prime n)
    (M : ℕ) {j : ℕ} (hj : 1 ≤ j) {σ : ℝ} (hσ : 0 < σ) (z Y : ℕ) (hz : 2 ≤ z)
    (hlogY : 0 < Real.log Y) :
    sieveMeanSquare (coeffBlock a (fun m => Nat.log 2 m) j) (Finset.Icc 1 M) σ z Y
      ≤ (((2 ^ (j + 1) : ℕ) : ℝ) * Real.log 4 / ((j : ℝ) * Real.log 2))
          * ((2 * (((2 ^ (j + 1) : ℕ) : ℝ)
                  * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
                / Real.log Y + selbergFibreError z Y + (z : ℝ))
              * ((A * (((j : ℝ) + 1) * Real.log 2)) ^ 2
                  * (2 : ℝ) ^ (-(2 * σ * (j : ℝ))))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine sieveMeanSquare_coeffBlock_le_of_bound (Bc := A * (((j : ℝ) + 1) * Real.log 2))
    (norm_coeffBlock_le_block_bound hA haB j) hprime M hj hσ z Y hz hlogY

end RHTower.Sieve
end
