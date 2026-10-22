import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Suzuki Volterra inverse-log grade recurrence

The trace-zero inverse of the principal physical boundary operator raises a power
`L⁻ᵅ` to `L⁻⁽ᵅ⁺¹⁾`.  This module certifies the exact coefficient forced by the differentiated
Volterra equation and proves that every positive grade retains a nonzero source coefficient.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exact coefficient produced when the trace-zero Volterra inverse raises inverse-log exponent
`α` by one. -/
def suzukiVolterraRaisedCoefficient (α : ℝ) (A : ℂ) : ℂ :=
  (α / (2 * α + 1) : ℝ) • A

/-- The raised coefficient solves the exact differentiated recurrence
`-(2α+1) C = -α A`. -/
theorem suzukiVolterraRaisedCoefficient_recurrence
    (α : ℝ) (A : ℂ) (hα : 2 * α + 1 ≠ 0) :
    -(2 * α + 1 : ℂ) * suzukiVolterraRaisedCoefficient α A =
      -(α : ℂ) * A := by
  have hcast : ((2 * α + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα
  rw [suzukiVolterraRaisedCoefficient, Complex.real_smul]
  push_cast at hcast ⊢
  field_simp [hcast]

/-- Positive inverse-log grade raising cannot erase a nonzero source coefficient. -/
theorem suzukiVolterraRaisedCoefficient_ne_zero
    {α : ℝ} (hα : 0 < α) {A : ℂ} (hA : A ≠ 0) :
    suzukiVolterraRaisedCoefficient α A ≠ 0 := by
  have hden : 2 * α + 1 ≠ 0 := by linarith
  have hquot : α / (2 * α + 1) ≠ 0 :=
    div_ne_zero (ne_of_gt hα) hden
  rw [suzukiVolterraRaisedCoefficient, Complex.real_smul]
  exact mul_ne_zero (by exact_mod_cast hquot) hA

/-- Every positive Volterra grade step contracts coefficient norm by at least the universal
factor `1 / 2`. -/
theorem norm_suzukiVolterraRaisedCoefficient_le_half
    {α : ℝ} (hα : 0 < α) (A : ℂ) :
    ‖suzukiVolterraRaisedCoefficient α A‖ ≤ (1 / 2 : ℝ) * ‖A‖ := by
  have hden : 0 < 2 * α + 1 := by linarith
  have hratio_nonneg : 0 ≤ α / (2 * α + 1) :=
    div_nonneg hα.le hden.le
  have hratio_le : α / (2 * α + 1) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  rw [suzukiVolterraRaisedCoefficient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hratio_nonneg]
  exact mul_le_mul_of_nonneg_right hratio_le (norm_nonneg A)

/-- Universal coefficient of the length-`k` physical prime-normal word expansion. -/
def suzukiPrimeNormalGradeFactor : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
      suzukiPrimeNormalGradeFactor k *
        (((2 * k + 1 : ℕ) : ℝ) / (4 * k + 4))

@[simp]
theorem suzukiPrimeNormalGradeFactor_zero :
    suzukiPrimeNormalGradeFactor 0 = 1 := rfl

@[simp]
theorem suzukiPrimeNormalGradeFactor_succ (k : ℕ) :
    suzukiPrimeNormalGradeFactor (k + 1) =
      suzukiPrimeNormalGradeFactor k *
        (((2 * k + 1 : ℕ) : ℝ) / (4 * k + 4)) := rfl

theorem suzukiPrimeNormalGradeFactor_pos (k : ℕ) :
    0 < suzukiPrimeNormalGradeFactor k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [suzukiPrimeNormalGradeFactor_succ]
      positivity

/-- The full length-`k` Volterra factor is at most `2⁻ᵏ`. -/
theorem suzukiPrimeNormalGradeFactor_le_half_pow (k : ℕ) :
    suzukiPrimeNormalGradeFactor k ≤ (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [suzukiPrimeNormalGradeFactor_succ, pow_succ]
      have hratio :
          (((2 * k + 1 : ℕ) : ℝ) / (4 * k + 4)) ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * k + 4)).mpr
        norm_num
        linarith
      calc
        suzukiPrimeNormalGradeFactor k *
            (((2 * k + 1 : ℕ) : ℝ) / (4 * k + 4)) ≤
            (1 / 2 : ℝ) ^ k * (((2 * k + 1 : ℕ) : ℝ) / (4 * k + 4)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ ≤ (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)

end

end GaloisForLFunctions.RHTower
