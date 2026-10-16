import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! # A compact input interval for a cutoff convolution kernel -/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry
attribute [local instance] Measure.Subtype.measureSpace

theorem exists_cutoff_kernel_interval {χ ρ : ℝ → ℝ}
    (hχ : HasCompactSupport χ) (hρ : HasCompactSupport ρ) :
    ∃ a : ℝ≥0, ∃ b : ℝ, ∀ x y, y ∉ Icc (0 : ℝ) (a : ℝ) →
      χ x * ρ (x + b - y) = 0 := by
  obtain ⟨R, hR, hbχ⟩ := hχ.isBounded.exists_pos_norm_le
  obtain ⟨S, hS, hbρ⟩ := hρ.isBounded.exists_pos_norm_le
  refine ⟨⟨2 * (R + S), by positivity⟩, R + S, ?_⟩
  intro x y hy
  change y ∉ Icc (0 : ℝ) (2 * (R + S)) at hy
  by_cases hx : χ x = 0
  · simp only [hx, zero_mul]
  by_cases hr : ρ (x + (R + S) - y) = 0
  · simp only [hr, mul_zero]
  have hbx := hbχ x (subset_tsupport χ hx)
  have hbr := hbρ (x + (R + S) - y) (subset_tsupport ρ hr)
  rw [Real.norm_eq_abs, abs_le] at hbx hbr
  exact (hy ⟨by linarith, by linarith⟩).elim

theorem cutoff_kernel_interval_eq_convolution (a : ℝ≥0) (b : ℝ) (χ ρ F : ℝ → ℝ)
    (hfit : ∀ x y, y ∉ Icc (0 : ℝ) (a : ℝ) → χ x * ρ (x + b - y) = 0)
    (x : ℝ) :
    (∫ y : Icc (0 : ℝ) (a : ℝ), F y * (χ x * ρ (x + b - y))) =
      ∫ s : ℝ, ρ s * (χ x * F (x + b - s)) := by
  rw [integral_subtype measurableSet_Icc (fun y : ℝ => F y * (χ x * ρ (x + b - y)))]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => by rw [hfit x y hy, mul_zero])]
  rw [← integral_sub_left_eq_self
    (fun y => F y * (χ x * ρ (x + b - y))) volume (x + b)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    rw [show x + b - (x + b - s) = s by ring]
    ring

end GaloisForLFunctions.HTGeometry
