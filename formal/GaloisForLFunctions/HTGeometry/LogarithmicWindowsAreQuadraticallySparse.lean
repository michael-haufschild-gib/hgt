import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Logarithmic windows are quadratically sparse

A linear window count with logarithmic local density is smaller than the
square of a suitable logarithmic radius. This supplies the escape budget for
quadratic ascent.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

private theorem log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

private theorem log_ten_thousand_one_le : Real.log (10001 : ℝ) ≤ 14 := by
  have hnum : (10001 : ℝ) ≤ (2 : ℝ) ^ 14 := by norm_num
  have h := Real.log_le_log (show (0 : ℝ) < 10001 by norm_num) hnum
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  nlinarith only [h, log_two_le_one]

/-- A logarithmic local count is beaten by the square of a logarithmic radius. -/
theorem exists_logarithmic_quadratic_window (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∃ R : ℝ, 0 < R ∧
      R ≤ C * Real.log (|t| + 3) ∧
      (2 * (⌈R⌉₊ : ℝ) + 1) *
        (16 * (K + Real.log (|t| + (⌈R⌉₊ : ℝ) + 4))) * (1 / 2) ^ 2 < R ^ 2 := by
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let D : ℝ := 1 + (K + 2) / Real.log 3
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  refine ⟨10000 * D, by positivity, fun t => ?_⟩
  let L : ℝ := 1 + K + Real.log (|t| + 5)
  let R : ℝ := 10000 * L
  have hlogt5 : 0 ≤ Real.log (|t| + 5) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hL0 : 0 < L := by linarith
  have hR : 0 < R := by dsimp only [R]; positivity
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith
  have hceil : (⌈R⌉₊ : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
  have hlog_window :
      Real.log (|t| + (⌈R⌉₊ : ℝ) + 4) ≤
        Real.log (|t| + 5) + Real.log (R + 1) := by
    have hsize : |t| + (⌈R⌉₊ : ℝ) + 4 ≤ (|t| + 5) * (R + 1) := by
      nlinarith only [hceil, abs_nonneg t, hR1]
    have h := Real.log_le_log (show 0 < |t| + (⌈R⌉₊ : ℝ) + 4 by positivity) hsize
    rw [Real.log_mul (by positivity : |t| + 5 ≠ 0) (by positivity : R + 1 ≠ 0)] at h
    exact h
  have hlog_radius : Real.log (R + 1) ≤ 14 + L := by
    have hsize : R + 1 ≤ 10001 * L := by dsimp only [R]; linarith
    have h := Real.log_le_log (show 0 < R + 1 by positivity) hsize
    rw [Real.log_mul (by norm_num : (10001 : ℝ) ≠ 0) hL0.ne'] at h
    have hlogL := Real.log_le_self hL0.le
    linarith [log_ten_thousand_one_le]
  have hterm : K + Real.log (|t| + (⌈R⌉₊ : ℝ) + 4) ≤ 15 * L := by
    dsimp only [L] at *
    linarith
  have hterm0 : 0 ≤ K + Real.log (|t| + (⌈R⌉₊ : ℝ) + 4) := by
    have harg : 1 ≤ |t| + (⌈R⌉₊ : ℝ) + 4 := by
      linarith [abs_nonneg t, Nat.cast_nonneg (α := ℝ) ⌈R⌉₊]
    have h := Real.log_nonneg harg
    linarith
  have hfactor : 2 * (⌈R⌉₊ : ℝ) + 1 ≤ 5 * R := by linarith
  have hproduct := mul_le_mul hfactor hterm hterm0 (show 0 ≤ 5 * R by positivity)
  have hbudget :
      (2 * (⌈R⌉₊ : ℝ) + 1) *
        (16 * (K + Real.log (|t| + (⌈R⌉₊ : ℝ) + 4))) ≤ 1200 * R * L := by
    nlinarith only [hproduct]
  have hbudget' := mul_le_mul_of_nonneg_right hbudget
    (show (0 : ℝ) ≤ (1 / 2) ^ 2 by positivity)
  have hquad :
      (2 * (⌈R⌉₊ : ℝ) + 1) *
        (16 * (K + Real.log (|t| + (⌈R⌉₊ : ℝ) + 4))) * (1 / 2) ^ 2 < R ^ 2 := by
    dsimp only [R] at hbudget' ⊢
    nlinarith only [hbudget', sq_pos_of_pos hL0]
  have hlog3t : Real.log 3 ≤ Real.log (|t| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog5 : Real.log (|t| + 5) ≤ Real.log 2 + Real.log (|t| + 3) := by
    have hsize : |t| + 5 ≤ 2 * (|t| + 3) := by linarith [abs_nonneg t]
    have h := Real.log_le_log (show 0 < |t| + 5 by positivity) hsize
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : |t| + 3 ≠ 0)] at h
    exact h
  have hquot : 0 ≤ (K + 2) / Real.log 3 := by positivity
  have hscale := mul_le_mul_of_nonneg_left hlog3t hquot
  have hscale_eq : ((K + 2) / Real.log 3) * Real.log 3 = K + 2 := by
    field_simp [hlog3.ne']
  rw [hscale_eq] at hscale
  have hLbound : L ≤ D * Real.log (|t| + 3) := by
    dsimp only [L, D]
    nlinarith only [hlog5, log_two_le_one, hscale]
  have hRbound : R ≤ (10000 * D) * Real.log (|t| + 3) := by
    dsimp only [R]
    nlinarith only [hLbound]
  exact ⟨R, hR, hRbound, hquad⟩

end GaloisForLFunctions.HTGeometry
