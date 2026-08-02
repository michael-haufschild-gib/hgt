import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.PSeries

/-!
# Dilated sums of a Schwartz function

Quadratic decay of a Schwartz function makes the sum of its dilates `sum_{n>=1} f(u n)` absolutely
convergent for every nonzero scale, with a bound `C / u^2` that is uniform in the scale.  This is
the estimate that makes the multiplicative Poisson sums of the co-Poisson theory absolutely
convergent and lets a sum and an integral be exchanged.
-/

open MeasureTheory SchwartzMap

noncomputable section

namespace HTGeometry

/-- Quadratic decay of a Schwartz function on the line. -/
theorem exists_sq_norm_bound (f : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ^ 2 * ‖f x‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := f.decay 2 0
  refine ⟨C, hCpos.le, fun x => ?_⟩
  have h := hC x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, sq_abs] at h
  exact h

theorem summable_inv_natSucc_sq : Summable fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹ := by
  have h : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
    have h2 := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa only [one_div] using h2
  have h1 := (summable_nat_add_iff 1).mpr h
  refine h1.congr fun n => ?_
  push_cast
  ring_nf

/-- The value of the comparison series for dilated Schwartz sums. -/
def schwartzDilateSeriesConstant : ℝ := ∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹

theorem schwartzDilateSeriesConstant_nonneg : 0 ≤ schwartzDilateSeriesConstant :=
  tsum_nonneg fun n => by positivity

/-- Termwise comparison: a dilated Schwartz value is at most `C / (u n)^2`. -/
theorem norm_schwartzDilate_le {f : SchwartzMap ℝ ℂ} {C : ℝ}
    (hC : ∀ x : ℝ, x ^ 2 * ‖f x‖ ≤ C) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    ‖f (u * ((n : ℝ) + 1))‖ ≤ C / u ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) < u * ((n : ℝ) + 1) := by positivity
  have h := hC (u * ((n : ℝ) + 1))
  rw [mul_pow] at h
  have hpos : (0 : ℝ) < u ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
  have hrw : C / u ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ = C / (u ^ 2 * ((n : ℝ) + 1) ^ 2) := by
    field_simp
  rw [hrw, le_div_iff₀ hpos, mul_comm]
  exact h

theorem summable_norm_schwartzDilate (f : SchwartzMap ℝ ℂ) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ => ‖f (u * ((n : ℝ) + 1))‖ := by
  obtain ⟨C, _, hC⟩ := exists_sq_norm_bound f
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_schwartzDilate_le hC hu n)
    (summable_inv_natSucc_sq.mul_left (C / u ^ 2))

theorem summable_schwartzDilate (f : SchwartzMap ℝ ℂ) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ => f (u * ((n : ℝ) + 1)) :=
  (summable_norm_schwartzDilate f hu).of_norm

/-- **Uniform bound on dilated Schwartz sums.**  The sum of the dilates of a Schwartz function at
scale `u` is at most a fixed multiple of `1 / u^2`. -/
theorem exists_tsum_norm_schwartzDilate_le (f : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u →
      ∑' n : ℕ, ‖f (u * ((n : ℝ) + 1))‖ ≤ C / u ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_sq_norm_bound f
  refine ⟨C * schwartzDilateSeriesConstant,
    mul_nonneg hC0 schwartzDilateSeriesConstant_nonneg, fun u hu => ?_⟩
  have hle := Summable.tsum_le_tsum (fun n => norm_schwartzDilate_le hC hu n)
    (summable_norm_schwartzDilate f hu) (summable_inv_natSucc_sq.mul_left (C / u ^ 2))
  rw [tsum_mul_left] at hle
  refine hle.trans_eq ?_
  rw [schwartzDilateSeriesConstant]
  ring

end HTGeometry
