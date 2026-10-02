import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanCofactors

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

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

def pmPowerDampedRamanujanLogSquareTerm (ε : ℝ) (q : ℕ) : ℝ :=
  (q : ℝ)*Real.log (2*(q : ℝ))*‖pmPowerDampedRamanujanWeight ε q‖^2

theorem pmPowerDampedRamanujanLogSquareTerm_nonneg (ε : ℝ) (q : ℕ) :
    0 ≤ pmPowerDampedRamanujanLogSquareTerm ε q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [pmPowerDampedRamanujanLogSquareTerm]
  · have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg q)
      (Real.log_nonneg (by linarith))) (sq_nonneg _)

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

theorem summable_pmPowerDampedRamanujanLogSquareTerm {ε : ℝ} (hε : 0 < ε) :
    Summable (pmPowerDampedRamanujanLogSquareTerm ε) := by
  apply Summable.of_nonneg_of_le (pmPowerDampedRamanujanLogSquareTerm_nonneg ε)
    (pmPowerDampedRamanujanLogSquareTerm_le hε)
  exact ((Real.summable_one_div_nat_rpow (p := 1+ε)).mpr (by linarith)).mul_left _

end RHTower
