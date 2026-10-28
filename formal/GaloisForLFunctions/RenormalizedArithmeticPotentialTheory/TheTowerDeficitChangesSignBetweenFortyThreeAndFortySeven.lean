import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSignOfTheTowerFinitePart
import GaloisForLFunctions.RHTower.ReversalPositivity
import GaloisForLFunctions.RHTower.HarmonicStirlingExactBounds

/-!
# The tower deficit changes sign between 43 and 47

The tower finite part of `p` is nonnegative on every depth iff the **tower deficit**
`d_p = √p log p/(p − 1) − γ` is `≤ 0` (`towerFinitePart_nonneg_iff`); `d_2 > 0` and `d_p ≤ 0` for
`p ≥ 2^16` (`towerDeficit_two_pos`, `towerDeficit_nonpos`). This file finds the exact threshold.

* **The deficit is `u/sinh u − γ`** (`towerDeficit_eq_div_sinh`): with `u = (log p)/2`,
  `√p = e^u` and `p − 1 = 2 e^u sinh u`, so `√p log p/(p − 1) = u/sinh u`.
* **Monotonicity** (`towerDeficit_strictAnti`): `u/sinh u` is strictly decreasing on `u > 0`, so
  `d_p` strictly decreases in `p`, from `d_2 ≈ 0.40` towards `−γ` (`neg_lt_towerDeficit`).
* **The two sides of the threshold** (`towerDeficit_fortyThree_pos`, `towerDeficit_fortySeven_neg`):
  `d_43 > 0 > d_47`, from `0.5753 < γ < 0.5777` (Euler–Maclaurin at `n = 4` and `n = 2`) and
  elementary bounds on `√43, log 43, √47, log 47`.
* **The sign table** (`towerDeficit_pos_iff`, `towerFinitePart_nonneg_iff_fortySeven_le`): for a
  prime `p`, `d_p > 0` iff `p ≤ 43`; the tower finite part of `p` is nonnegative on every depth iff
  `p ≥ 47`.

So exactly the fourteen primes `2, 3, …, 43` carry a positive deficit `2d_p`, and the ledger of
small-prime payments is finite and explicit: every larger prime pays for its own classes.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

/-- **The tower ratio is `u/sinh u`**: for `x > 1`, `√x log x/(x − 1) = u/sinh u`,
`u = (log x)/2`. -/
theorem sqrt_mul_log_div_eq_div_sinh {x : ℝ} (hx : 1 < x) :
    Real.sqrt x * Real.log x / (x - 1) = (Real.log x / 2) / Real.sinh (Real.log x / 2) := by
  have hx0 : 0 < x := by linarith
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hexp : Real.exp (Real.log x / 2) = s := by
    rw [hs, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  -- `sinh u = (s − 1/s)/2 = (x − 1)/(2s)`
  have hsinh : Real.sinh (Real.log x / 2) = (x - 1) / (2 * s) := by
    rw [Real.sinh_eq, Real.exp_neg, hexp, ← hss]
    field_simp
  have hx1 : x - 1 ≠ 0 := by linarith
  rw [hsinh]
  field_simp

/-- **The tower deficit is `u/sinh u − γ`**, `u = (log p)/2`. -/
theorem towerDeficit_eq_div_sinh {p : ℕ} (hp : 2 ≤ p) :
    towerDeficit p = (Real.log p / 2) / Real.sinh (Real.log p / 2) - γ := by
  rw [towerDeficit, sqrt_mul_log_div_eq_div_sinh (by exact_mod_cast (show 1 < p by omega))]

theorem half_log_pos {p : ℕ} (hp : 2 ≤ p) : 0 < Real.log p / 2 :=
  half_pos (Real.log_pos (by exact_mod_cast (show 1 < p by omega)))

/-- **The tower deficit decreases strictly**: `d_q < d_p` for `2 ≤ p < q`. -/
theorem towerDeficit_strictAnti {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) :
    towerDeficit q < towerDeficit p := by
  rw [towerDeficit_eq_div_sinh hp, towerDeficit_eq_div_sinh (by omega)]
  have hlp := half_log_pos hp
  have hlt : Real.log p / 2 < Real.log q / 2 := by
    have := Real.log_lt_log (by exact_mod_cast (show 0 < p by omega)) (by exact_mod_cast hpq :
      (p : ℝ) < q)
    linarith
  have h := RHTower.div_sinh_strictAntiOn hlp (hlp.trans hlt) hlt
  simp only at h
  linarith

/-- The deficit stays above its limit: `−γ < d_p`. -/
theorem neg_lt_towerDeficit {p : ℕ} (hp : 2 ≤ p) : -γ < towerDeficit p := by
  rw [towerDeficit_eq_div_sinh hp]
  have hu := half_log_pos hp
  have := div_pos hu (Real.sinh_pos_iff.mpr hu)
  linarith

/-- `0.5753 < γ`, from the Euler–Maclaurin bound at `n = 4`. -/
theorem eulerMascheroniConstant_gt_d4 : (0.5753 : ℝ) < γ := by
  have h := RHTower.harmonic_mascheroni_le_half_sub_twelfth (n := 4) (by norm_num)
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  norm_num [harmonic, Finset.sum_range_succ, he] at h
  linarith [Real.log_two_lt_d9]

/-- `γ < 0.5777`, from the Euler–Maclaurin bound at `n = 2`. -/
theorem eulerMascheroniConstant_lt_d4 : γ < (0.5777 : ℝ) := by
  have h := RHTower.harmonic_mascheroni_ge_half_sub_twelfth (n := 2) (by norm_num)
  norm_num [harmonic, Finset.sum_range_succ] at h
  linarith [Real.log_two_gt_d9]

/-- **`d_43 > 0`**: `√43 log 43 > 6.557 (5 log 2 + 11/43) > 42 γ`. -/
theorem towerDeficit_fortyThree_pos : 0 < towerDeficit 43 := by
  have hs : (6.557 : ℝ) < Real.sqrt 43 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  -- `log 43 = 5 log 2 + log(43/32) ≥ 5 log 2 + 11/43`
  have hlog : 5 * Real.log 2 + 11 / 43 ≤ Real.log 43 := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 43 / 32 by norm_num)
    have h2 : Real.log 43 = Real.log 32 + Real.log (43 / 32) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h3 : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
      norm_num
    norm_num at h1
    linarith
  have hl2 := Real.log_two_gt_d9
  have hprod : 6.557 * (5 * Real.log 2 + 11 / 43) ≤ Real.sqrt 43 * Real.log 43 :=
    mul_le_mul hs.le hlog (by linarith) (Real.sqrt_nonneg _)
  have hγ := eulerMascheroniConstant_lt_d4
  have hd : towerDeficit 43 = Real.sqrt 43 * Real.log 43 / 42 - γ := by
    unfold towerDeficit
    norm_num
  rw [hd, sub_pos, lt_div_iff₀ (by norm_num)]
  norm_num at hl2
  linarith

/-- **`d_47 < 0`**: `√47 log 47 < 6.8557 (4 log 2 + log 3 − 1/48) < 46 γ`. -/
theorem towerDeficit_fortySeven_neg : towerDeficit 47 < 0 := by
  have hs : Real.sqrt 47 < 6.8557 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  -- `log 47 = log 48 + log(47/48) ≤ 4 log 2 + log 3 − 1/48`
  have hlog : Real.log 47 ≤ 4 * Real.log 2 + Real.log 3 - 1 / 48 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 47 / 48 by norm_num)
    have h2 : Real.log 47 = Real.log 48 + Real.log (47 / 48) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h3 : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
      rw [show (48 : ℝ) = 2 ^ (4 : ℕ) * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      norm_num
    norm_num at h1
    linarith
  have hl0 : 0 ≤ Real.log 47 := Real.log_nonneg (by norm_num)
  have hprod : Real.sqrt 47 * Real.log 47 ≤ 6.8557 * (4 * Real.log 2 + Real.log 3 - 1 / 48) :=
    mul_le_mul hs.le hlog hl0 (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hl3 := Real.log_three_lt_d9
  have hγ := eulerMascheroniConstant_gt_d4
  have hd : towerDeficit 47 = Real.sqrt 47 * Real.log 47 / 46 - γ := by
    unfold towerDeficit
    norm_num
  rw [hd, sub_neg, div_lt_iff₀ (by norm_num)]
  norm_num at hl2 hl3
  linarith

/-- **Small primes carry a deficit**: `d_n > 0` for `2 ≤ n ≤ 43`. -/
theorem towerDeficit_pos_of_le {n : ℕ} (hn : 2 ≤ n) (hn43 : n ≤ 43) : 0 < towerDeficit n := by
  rcases hn43.lt_or_eq with h | h
  · exact towerDeficit_fortyThree_pos.trans (towerDeficit_strictAnti hn h)
  · rw [h]
    exact towerDeficit_fortyThree_pos

/-- **Large primes pay for their classes**: `d_n < 0` for `n ≥ 47`. -/
theorem towerDeficit_neg_of_le {n : ℕ} (hn : 47 ≤ n) : towerDeficit n < 0 := by
  rcases hn.lt_or_eq with h | h
  · exact (towerDeficit_strictAnti (by norm_num) h).trans towerDeficit_fortySeven_neg
  · rw [← h]
    exact towerDeficit_fortySeven_neg

/-- **The sign table**: for a prime `p`, `d_p > 0` iff `p ≤ 43`. -/
theorem towerDeficit_pos_iff {p : ℕ} (hp : p.Prime) : 0 < towerDeficit p ↔ p ≤ 43 := by
  refine ⟨fun h => ?_, fun h => towerDeficit_pos_of_le hp.two_le h⟩
  by_contra hgt
  -- no prime lies strictly between 43 and 47
  have h47 : 47 ≤ p := by
    by_contra h'
    interval_cases p <;> norm_num at hp
  exact (towerDeficit_neg_of_le h47).not_gt h

/-- **The tower finite part of `p` is nonnegative on every depth iff `p ≥ 47`.** -/
theorem towerFinitePart_nonneg_iff_fortySeven_le {p : ℕ} (hp : p.Prime) :
    (∀ (N : ℕ) (b : ℕ → ℝ), 0 ≤ towerFinitePart p N b) ↔ 47 ≤ p := by
  rw [towerFinitePart_nonneg_iff hp]
  constructor
  · intro h
    by_contra hlt
    exact h.not_gt (towerDeficit_pos_of_le hp.two_le (by
      by_contra h'
      interval_cases p <;> norm_num at hp))
  · intro h
    exact (towerDeficit_neg_of_le h).le

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
