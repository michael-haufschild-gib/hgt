import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanCofactors

/-!
# Pointwise decay and logarithmic square mass of the Ramanujan weights

From the cofactor bound `|K_q(q)| = q|w_ε(q)| ≤ q^(−ε)` the power-damped Ramanujan weights
satisfy `|w_ε(q)| ≤ q^(−1−ε)` for `ε > 0`. Combined with `log(2q) ≤ (2^ε/ε) q^ε`, this gives
convergence of the logarithmic square mass `∑_q q log(2q) |w_ε(q)|²`, each term being at most
`(2^ε/ε) q^(−1−ε)`.

## Main results

- `norm_pmPowerDampedRamanujanWeight_le`: `|w_ε(q)| ≤ 1/q^(1+ε)` for `ε > 0`, `q > 0`.
- `pmPowerDampedRamanujanLogSquareTerm_le`: `q log(2q) |w_ε(q)|² ≤ (2^ε/ε)/q^(1+ε)`.
- `summable_pmPowerDampedRamanujanLogSquareTerm`: `∑_q q log(2q) |w_ε(q)|²` converges for `ε > 0`.

## Hypotheses

All results are unconditional; they assume only `0 < ε` (and `0 < q` for the pointwise bound).
The summability constant `2^ε/ε` blows up as `ε → 0⁺`; no uniformity in `ε` is claimed.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- For `ε > 0` and `q > 0`, the Ramanujan weight decays as `|w_ε(q)| ≤ 1/q^(1+ε)`. -/
theorem norm_pmPowerDampedRamanujanWeight_le {ε : ℝ} (hε : 0 < ε)
    {q : ℕ} (hq : 0 < q) :
    ‖pmPowerDampedRamanujanWeight ε q‖ ≤ 1/(q : ℝ)^(1+ε) := by
  have h := norm_pmPowerDampedRamanujanCofactor_le hε q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : (q : ℝ)*‖pmPowerDampedRamanujanWeight ε q‖ ≤ (q : ℝ)^(-ε) := by
    simpa [pmPowerDampedRamanujanCofactor, Nat.div_self hq] using h
  calc
    _ ≤ (q : ℝ)^(-ε)/(q : ℝ) :=
      (le_div_iff₀ hqR).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by
      rw [Real.rpow_add hqR, Real.rpow_one, Real.rpow_neg hqR.le]
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- The logarithmic square-mass term `q log(2q) |w_ε(q)|²`. -/
def pmPowerDampedRamanujanLogSquareTerm (ε : ℝ) (q : ℕ) : ℝ :=
  (q : ℝ)*Real.log (2*(q : ℝ))*‖pmPowerDampedRamanujanWeight ε q‖^2

theorem pmPowerDampedRamanujanLogSquareTerm_nonneg (ε : ℝ) (q : ℕ) :
    0 ≤ pmPowerDampedRamanujanLogSquareTerm ε q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [pmPowerDampedRamanujanLogSquareTerm]
  · have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg q)
      (Real.log_nonneg (by linarith))) (sq_nonneg _)

/-- For `ε > 0`, `q log(2q) |w_ε(q)|² ≤ (2^ε/ε) · 1/q^(1+ε)`. -/
theorem pmPowerDampedRamanujanLogSquareTerm_le {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    pmPowerDampedRamanujanLogSquareTerm ε q ≤
      ((2 : ℝ)^ε/ε)*(1/(q : ℝ)^(1+ε)) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [pmPowerDampedRamanujanLogSquareTerm, Real.zero_rpow (by linarith : 1+ε ≠ 0)]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log (2*(q : ℝ)) ≤ ((2 : ℝ)^ε/ε)*(q : ℝ)^ε := by
    refine (Real.log_le_rpow_div (by positivity) hε).trans_eq ?_
    rw [Real.mul_rpow (by norm_num) hqR.le]
    ring
  have hnorm := norm_pmPowerDampedRamanujanWeight_le hε hq
  calc
    _ ≤ (q : ℝ)*(((2 : ℝ)^ε/ε)*(q : ℝ)^ε)*(1/(q : ℝ)^(1+ε))^2 := by
      dsimp only [pmPowerDampedRamanujanLogSquareTerm]
      gcongr
    _ = _ := by
      rw [Real.rpow_add hqR, Real.rpow_one]
      have hp : (q : ℝ)^ε ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hqR ε)
      field_simp

/-- For `ε > 0`, the logarithmic square mass `∑_q q log(2q) |w_ε(q)|²` converges. -/
theorem summable_pmPowerDampedRamanujanLogSquareTerm {ε : ℝ} (hε : 0 < ε) :
    Summable (pmPowerDampedRamanujanLogSquareTerm ε) := by
  apply Summable.of_nonneg_of_le (pmPowerDampedRamanujanLogSquareTerm_nonneg ε)
    (pmPowerDampedRamanujanLogSquareTerm_le hε)
  exact ((Real.summable_one_div_nat_rpow (p := 1+ε)).mpr (by linarith)).mul_left _

end RHTower
