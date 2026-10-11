import Mathlib

/-! Unit-circle tests transfer finite probability estimates without moment growth. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilPhase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

theorem finiteWeilPhase_norm (x : ℝ) : ‖finiteWeilPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem finiteWeilPhase_sub_norm_le (x y : ℝ) :
    ‖finiteWeilPhase x - finiteWeilPhase y‖ ≤ |x - y| := by
  have hmul : finiteWeilPhase y * finiteWeilPhase (x - y) = finiteWeilPhase x := by
    unfold finiteWeilPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ‖finiteWeilPhase y * (finiteWeilPhase (x - y) - 1)‖ := by
      rw [mul_sub, mul_one, hmul]
    _ = ‖finiteWeilPhase (x - y) - 1‖ := by rw [norm_mul, finiteWeilPhase_norm, one_mul]
    _ = ‖2 * Real.sin ((x - y) / 2)‖ := by
      unfold finiteWeilPhase
      rw [mul_comm (((x - y : ℝ) : ℂ)) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    _ = 2 * |Real.sin ((x - y) / 2)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * |(x - y) / 2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring

theorem finiteWeilPhase_weight_error {ι : Type*} [Fintype ι]
    (p q f : ι → ℝ) :
    ‖(∑ i, (p i : ℂ) * finiteWeilPhase (f i)) - ∑ i, (q i : ℂ) * finiteWeilPhase (f i)‖ ≤
      ∑ i, |p i - q i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(p i : ℂ) * finiteWeilPhase (f i) - (q i : ℂ) * finiteWeilPhase (f i)‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, finiteWeilPhase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs]

theorem finiteWeilPhase_phase_error {ι : Type*} [Fintype ι]
    (p f g : ι → ℝ) :
    ‖(∑ i, (p i : ℂ) * finiteWeilPhase (f i)) - ∑ i, (p i : ℂ) * finiteWeilPhase (g i)‖ ≤
      ∑ i, |p i| * |f i - g i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(p i : ℂ) * finiteWeilPhase (f i) - (p i : ℂ) * finiteWeilPhase (g i)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (finiteWeilPhase_sub_norm_le (f i) (g i)) (abs_nonneg _)

end RHTower
