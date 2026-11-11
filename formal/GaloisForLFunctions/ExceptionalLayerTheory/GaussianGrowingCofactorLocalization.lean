import GaloisForLFunctions.ExceptionalLayerTheory.GaussianGrowingMomentReduction
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherCofactorTail

/-!
# Polynomial cofactor localization at exponential scales

Growing Gaussian moments allow an almost full-scale long cutoff.
The remaining cofactor range is polynomial in height, while both the
Vaughan reduction error and the discarded arithmetic tail decay exponentially.
-/

open Complex Finset Filter Topology RHTower ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A polynomial-height cofactor cutoff beyond the Gaussian tail horizon. -/
def gaussianGrowingCofactorCutoff (J : ℕ) (t : ℝ) : ℕ := ⌈2 * t ^ (J + 3)⌉₊

/-- The rounded cutoffs reach the required tail horizon with a polynomial
number of cofactors. -/
theorem eventually_gaussianGrowingCofactorCutoff_bounds {a : ℝ} (ha : 0 < a) (J : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      Real.exp (a * t) * t ^ 2 ≤
        ((gaussianGrowingLongCutoff a J t * gaussianGrowingCofactorCutoff J t : ℕ) : ℝ) ∧
      (gaussianGrowingCofactorCutoff J t : ℝ) ≤ 3 * t ^ (J + 3) := by
  filter_upwards [eventually_gaussianGrowingLongCutoff_bounds ha J,
    eventually_ge_atTop (1 : ℝ)] with t hcut ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hU := hcut.2.2.2.2
  have hW : 2 * t ^ (J + 3) ≤ (gaussianGrowingCofactorCutoff J t : ℝ) := Nat.le_ceil _
  have hprod : Real.exp (a * t) * t ^ 2 ≤
      ((gaussianGrowingLongCutoff a J t * gaussianGrowingCofactorCutoff J t : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    calc
      _ = (Real.exp (a * t) / (2 * t ^ (J + 1))) * (2 * t ^ (J + 3)) := by
        rw [show J + 3 = (J + 1) + 2 by omega, pow_add]
        field_simp
        rw [← pow_add]
        congr 1
        omega
      _ ≤ _ := mul_le_mul hU hW (by positivity) (Nat.cast_nonneg _)
  have hceil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * t ^ (J + 3))
  have hpow : (1 : ℝ) ≤ t ^ (J + 3) := one_le_pow₀ ht
  have hupper : (gaussianGrowingCofactorCutoff J t : ℝ) ≤ 3 * t ^ (J + 3) := by
    change (⌈2 * t ^ (J + 3)⌉₊ : ℝ) ≤ _
    linarith only [hceil, hpow]
  exact ⟨hprod, hupper⟩

/-- At exponential observation scales, the actual centred current can be
restricted to polynomially many cofactors with an exponentially small error. -/
theorem eventually_gaussianGrowingMomentCofactorReduction {a κ : ℝ} (ha : 0 < a)
    (hκ : 0 < κ) (hκa : κ ≤ a / 32) (J : ℕ) (hJ : 4 ≤ J)
    (hJκ : 2 * a ≤ ((2 * J - 7 : ℕ) : ℝ) * κ) :
    ∀ᶠ t : ℝ in atTop, ∀ ε : ℂ, 0 < ε.re → ‖ε‖ ≤ 4 * ε.re * t →
      ε.re * (Real.exp (a * t)) ^ 2 = 2 →
      ‖((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          gaussianHigherPrimeMomentWeight (gaussianGrowingMomentOrder κ t) (1 / 2) t ε n) -
        gaussianHigherMomentPole (gaussianGrowingMomentOrder κ t) ((1 / 2 : ℂ) + t * I) ε t) -
        gaussianHigherCentredVaughanCofactorCurrent (gaussianGrowingMomentOrder κ t)
          (1 / 2) t ε (gaussianGrowingLongCutoff a J t) ⌊t⌋₊
            (gaussianGrowingCofactorCutoff J t)‖ ≤
        (gaussianGrowingMomentConstant + 784) * Real.exp (-(a / 4) * t) := by
  filter_upwards [eventually_gaussianGrowingMomentReduction ha hκ hκa J hJ hJκ,
    eventually_gaussianGrowingMomentOrder_bounds hκ,
    eventually_gaussianGrowingCofactorCutoff_bounds ha J,
    eventually_ge_atTop (max 8192 (3 * a))] with t hred hr hcut ht
  intro ε hε hsector hscale
  have ht32 : 32 ≤ t := by have hh := (le_max_left _ _).trans ht; linarith only [hh]
  have ht0 : 0 < t := by linarith only [ht32]
  have hat : 3 * a ≤ t := (le_max_right _ _).trans ht
  have he := gaussianHigherCentredVaughan_sub_cofactorCurrent_eq
    (gaussianGrowingMomentOrder κ t) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    ht0 hε hsector (gaussianGrowingLongCutoff a J t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff J t)
  have htail := norm_gaussianHigherVaughanCofactorTail_le_exp_neg_sq
    (gaussianGrowingMomentOrder κ t) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    ha ht32 hat hr.2.1 hε hsector hscale
    (gaussianGrowingLongCutoff a J t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff J t) hcut.1
  have hsum : ((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          gaussianHigherPrimeMomentWeight (gaussianGrowingMomentOrder κ t) (1 / 2) t ε n) -
        gaussianHigherMomentPole (gaussianGrowingMomentOrder κ t) ((1 / 2 : ℂ) + t * I) ε t) -
        gaussianHigherCentredVaughanCofactorCurrent (gaussianGrowingMomentOrder κ t)
          (1 / 2) t ε (gaussianGrowingLongCutoff a J t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff J t) =
      gaussianHigherCentredVaughanError (gaussianGrowingMomentOrder κ t) (1 / 2) t
          (gaussianGrowingLongCutoff a J t) ⌊t⌋₊ ε +
        gaussianHigherVaughanCofactorTail (gaussianGrowingMomentOrder κ t) (1 / 2) t
          (gaussianGrowingLongCutoff a J t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff J t) ε := by
    rw [← he]
    unfold gaussianHigherCentredVaughanError
    have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hhalf]
    ring
  rw [hsum]
  have htExp : Real.exp (-t ^ 2) ≤ Real.exp (-(a / 4) * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hat ht0.le, mul_pos ha ht0]
  calc
    _ ≤ ‖gaussianHigherCentredVaughanError (gaussianGrowingMomentOrder κ t) (1 / 2) t
        (gaussianGrowingLongCutoff a J t) ⌊t⌋₊ ε‖ +
        ‖gaussianHigherVaughanCofactorTail (gaussianGrowingMomentOrder κ t) (1 / 2) t
          (gaussianGrowingLongCutoff a J t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff J t) ε‖ := norm_add_le _ _
    _ ≤ gaussianGrowingMomentConstant * Real.exp (-(a / 4) * t) + 784 * Real.exp (-t ^ 2) :=
      _root_.add_le_add (hred ε hε hsector hscale) htail
    _ ≤ _ := by nlinarith only [htExp]

end GaloisForLFunctions.ExceptionalLayerTheory
