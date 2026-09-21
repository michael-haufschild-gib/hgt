import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar source-successor compensation for the Hellinger Gamma gauge

The even Gamma residue gauge has size `1 / (2 n)!`.  The literal `2 → 3`
source successor has norm `(3 / 2)^(m / 2)`.  Selecting the least depth
whose successor norm reaches `(2 n)!` produces a bounded, non-vanishing
combined coefficient.  This lightweight leaf proves scalar calibration using
only its explicit factorial formula.  The later source-interface leaf will
identify this gauge with the existing Hellinger residue.
-/

namespace RHTower

noncomputable section

namespace HellingerGammaSuccessorCompensation

/-- Least `2 → 3` successor depth that compensates the even Gamma residue. -/
def compensationDepth (n : ℕ) : ℕ :=
  Nat.ceil
    (2 * Real.log (((2 * n).factorial : ℝ)) / Real.log (3 / 2 : ℝ))

/-- Scalar norm of the compensating successor transport. -/
def compensationScale (n : ℕ) : ℝ :=
  (3 / 2 : ℝ) ^ ((compensationDepth n : ℝ) / 2)

/-- Explicit even Gamma residue gauge.  The source-interface leaf identifies it
with the existing Hellinger residue coordinate. -/
def evenGammaResidueGauge (n : ℕ) : ℝ :=
  ((2 * n).factorial : ℝ)⁻¹

/-- Explicit Gamma gauge after the compensating `2 → 3` successor transport. -/
def compensatedGammaResidue (n : ℕ) : ℝ :=
  evenGammaResidueGauge n * compensationScale n

private theorem twoThree_pos : (0 : ℝ) < 3 / 2 := by norm_num

private theorem one_lt_twoThree : (1 : ℝ) < 3 / 2 := by norm_num

private theorem log_twoThree_pos : (0 : ℝ) < Real.log (3 / 2 : ℝ) :=
  Real.log_pos one_lt_twoThree

private theorem factorial_pos (n : ℕ) : (0 : ℝ) < ((2 * n).factorial : ℝ) := by
  positivity

private theorem log_factorial_nonneg (n : ℕ) :
    0 ≤ Real.log ((2 * n).factorial : ℝ) := by
  apply Real.log_nonneg
  have hfac : 0 < (2 * n).factorial := Nat.factorial_pos _
  exact_mod_cast (show 1 ≤ (2 * n).factorial by omega)

private theorem target_le_compensationDepth (n : ℕ) :
    2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ) ≤
      (compensationDepth n : ℝ) := by
  exact Nat.le_ceil _

private theorem compensationDepth_lt_target_add_one (n : ℕ) :
    (compensationDepth n : ℝ) <
      2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ) + 1 := by
  apply Nat.ceil_lt_add_one
  exact div_nonneg (mul_nonneg (by norm_num) (log_factorial_nonneg n))
    log_twoThree_pos.le

private theorem target_scale_eq_factorial (n : ℕ) :
    (3 / 2 : ℝ) ^
        ((2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ)) / 2) =
      ((2 * n).factorial : ℝ) := by
  calc
    (3 / 2 : ℝ) ^
        ((2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ)) / 2) =
      Real.exp
        (Real.log (3 / 2 : ℝ) *
          ((2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ)) / 2)) :=
      Real.rpow_def_of_pos twoThree_pos _
    _ = Real.exp (Real.log ((2 * n).factorial : ℝ)) := by
      congr 1
      field_simp [log_twoThree_pos.ne']
    _ = ((2 * n).factorial : ℝ) := Real.exp_log (factorial_pos n)

private theorem factorial_le_compensationScale (n : ℕ) :
    ((2 * n).factorial : ℝ) ≤ compensationScale n := by
  have hhalf :
      (2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ)) / 2 ≤
        (compensationDepth n : ℝ) / 2 := by
    linarith [target_le_compensationDepth n]
  calc
    ((2 * n).factorial : ℝ) =
        (3 / 2 : ℝ) ^
          ((2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ)) / 2) :=
      (target_scale_eq_factorial n).symm
    _ ≤ compensationScale n := by
      exact Real.rpow_le_rpow_of_exponent_le one_lt_twoThree.le hhalf

private theorem compensationScale_lt_factorial_mul_halfPower (n : ℕ) :
    compensationScale n <
      ((2 * n).factorial : ℝ) * (3 / 2 : ℝ) ^ ((1 : ℝ) / 2) := by
  have hhalf :
      (compensationDepth n : ℝ) / 2 <
        (2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ)) / 2 +
          (1 : ℝ) / 2 := by
    linarith [compensationDepth_lt_target_add_one n]
  calc
    compensationScale n <
        (3 / 2 : ℝ) ^
          ((2 * Real.log ((2 * n).factorial : ℝ) / Real.log (3 / 2 : ℝ)) / 2 +
            (1 : ℝ) / 2) := by
      exact Real.rpow_lt_rpow_of_exponent_lt one_lt_twoThree hhalf
    _ = ((2 * n).factorial : ℝ) * (3 / 2 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_add twoThree_pos, target_scale_eq_factorial n]

/-- Compensation removes the factorial collapse: the combined coefficient is at least one. -/
theorem one_le_compensatedGammaResidue (n : ℕ) :
    1 ≤ compensatedGammaResidue n := by
  rw [compensatedGammaResidue, evenGammaResidueGauge]
  calc
    1 = ((2 * n).factorial : ℝ)⁻¹ * ((2 * n).factorial : ℝ) :=
      (inv_mul_cancel₀ (factorial_pos n).ne').symm
    _ ≤ ((2 * n).factorial : ℝ)⁻¹ * compensationScale n :=
      mul_le_mul_of_nonneg_left (factorial_le_compensationScale n)
        (inv_nonneg.mpr (factorial_pos n).le)

/-- Ceiling calibration bounds the combined coefficient by the next half-step. -/
theorem compensatedGammaResidue_lt_twoThree_halfPower (n : ℕ) :
    compensatedGammaResidue n < (3 / 2 : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [compensatedGammaResidue, evenGammaResidueGauge]
  rw [inv_mul_lt_iff₀ (factorial_pos n)]
  simpa [mul_comm] using compensationScale_lt_factorial_mul_halfPower n

private theorem twoThree_halfPower_sq :
    ((3 / 2 : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = 3 / 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul twoThree_pos.le]
  norm_num

/-- Multiplication by the calibrated source-successor gauge preserves and
reflects uniform boundedness of every nonnegative capacity.  Thus it removes
the factorial vertical collapse without erasing the exact bounded/unbounded
classification carried by a two-channel capacity. -/
theorem compensatedGammaResidue_uniformBound_iff
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    (∃ C : ℝ, ∀ n : ℕ, compensatedGammaResidue n ^ 2 * f n ≤ C) ↔
      ∃ C : ℝ, ∀ n : ℕ, f n ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => ?_⟩
    have hres : 1 ≤ compensatedGammaResidue n :=
      one_le_compensatedGammaResidue n
    have hsq : 1 ≤ compensatedGammaResidue n ^ 2 := by
      nlinarith [sq_nonneg (compensatedGammaResidue n - 1)]
    calc
      f n = 1 * f n := by ring
      _ ≤ compensatedGammaResidue n ^ 2 * f n :=
        mul_le_mul_of_nonneg_right hsq (hf n)
      _ ≤ C := hC n
  · rintro ⟨C, hC⟩
    refine ⟨(3 / 2 : ℝ) * C, fun n => ?_⟩
    have hres0 : 0 ≤ compensatedGammaResidue n :=
      (le_trans zero_le_one (one_le_compensatedGammaResidue n))
    have hhalf0 : 0 ≤ (3 / 2 : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg twoThree_pos.le _
    have hsq : compensatedGammaResidue n ^ 2 ≤ 3 / 2 := by
      calc
        compensatedGammaResidue n ^ 2 ≤
            ((3 / 2 : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 :=
          (sq_le_sq₀ hres0 hhalf0).mpr
            (compensatedGammaResidue_lt_twoThree_halfPower n).le
        _ = 3 / 2 := twoThree_halfPower_sq
    calc
      compensatedGammaResidue n ^ 2 * f n ≤ (3 / 2 : ℝ) * f n :=
        mul_le_mul_of_nonneg_right hsq (hf n)
      _ ≤ (3 / 2 : ℝ) * C :=
        mul_le_mul_of_nonneg_left (hC n) twoThree_pos.le

end HellingerGammaSuccessorCompensation

end

end RHTower
