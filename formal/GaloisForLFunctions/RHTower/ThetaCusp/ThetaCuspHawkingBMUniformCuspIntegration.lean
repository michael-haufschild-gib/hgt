import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
Uniform all-weight cusp decay implies an all-weight vanishing horizontal
boundary integral.  This is the finite-width analytic bridge needed when a
literal Fourier current has estimates uniform in its horizontal coordinate.
-/

open Set Filter Topology MeasureTheory

namespace RHTower.D4BMUniformCuspIntegration

set_option autoImplicit false

/-- A two-coordinate complex cusp field. -/
abbrev Field := ℝ → ℝ → ℂ

/-- Every complex height weight is bounded uniformly across a horizontal strip. -/
def UniformCuspRapid (f : Field) : Prop :=
  ∀ w : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, 1 ≤ y →
    ‖(y : ℂ) ^ w * f x y‖ ≤ C

theorem UniformCuspRapid.add {f g : Field}
    (hf : UniformCuspRapid f) (hg : UniformCuspRapid g) :
    UniformCuspRapid (fun x y => f x y + g x y) := by
  intro w
  obtain ⟨A, hA, ha⟩ := hf w
  obtain ⟨B, hB, hb⟩ := hg w
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro x y hy
  rw [mul_add]
  exact (norm_add_le _ _).trans (add_le_add (ha x y hy) (hb x y hy))

theorem UniformCuspRapid.scale (c : ℂ) {f : Field}
    (hf : UniformCuspRapid f) :
    UniformCuspRapid (fun x y => c * f x y) := by
  intro w
  obtain ⟨A, hA, ha⟩ := hf w
  refine ⟨‖c‖ * A, mul_nonneg (norm_nonneg _) hA, ?_⟩
  intro x y hy
  rw [mul_left_comm, norm_mul]
  exact mul_le_mul_of_nonneg_left (ha x y hy) (norm_nonneg _)

theorem UniformCuspRapid.cpow (v : ℂ) {f : Field}
    (hf : UniformCuspRapid f) :
    UniformCuspRapid (fun x y => (y : ℂ) ^ v * f x y) := by
  intro w
  obtain ⟨A, hA, ha⟩ := hf (w + v)
  refine ⟨A, hA, ?_⟩
  intro x y hy
  rw [← mul_assoc, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hy).ne')]
  exact ha x y hy

theorem UniformCuspRapid.mul {f g : Field}
    (hf : UniformCuspRapid f) (hg : UniformCuspRapid g) :
    UniformCuspRapid (fun x y => f x y * g x y) := by
  intro w
  obtain ⟨A, hA, ha⟩ := hf w
  obtain ⟨B, hB, hb⟩ := hg 0
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro x y hy
  have hgb : ‖g x y‖ ≤ B := by
    simpa only [Complex.cpow_zero, one_mul] using hb x y hy
  rw [← mul_assoc, norm_mul]
  exact mul_le_mul (ha x y hy) hgb (norm_nonneg _) hA

theorem UniformCuspRapid.congr {f g : Field}
    (hf : UniformCuspRapid f)
    (he : ∀ x y : ℝ, 1 ≤ y → f x y = g x y) :
    UniformCuspRapid g := by
  intro w
  obtain ⟨C, hC, hb⟩ := hf w
  exact ⟨C, hC, fun x y hy => by rw [← he x y hy]; exact hb x y hy⟩

/-- A uniform all-weight bound makes the width-one horizontal cusp integral
vanish after every complex height weight. -/
theorem UniformCuspRapid.integral_vanish {f : Field}
    (hf : UniformCuspRapid f) (w : ℂ) :
    Tendsto (fun y : ℝ => ∫ x in (-1 / 2 : ℝ)..1 / 2,
      (y : ℂ) ^ w * f x y) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := hf (w + 1)
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [eventually_ge_atTop (max 1 (C / epsilon + 1))] with y hy
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hyC : C / epsilon + 1 ≤ y := (le_max_right _ _).trans hy
  have hCy : C / y < epsilon := by
    apply (div_lt_iff₀ hy0).2
    have he : C / epsilon * epsilon = C := div_mul_cancel₀ C hepsilon.ne'
    nlinarith
  have hbound (x : ℝ) : ‖(y : ℂ) ^ w * f x y‖ ≤ C / y := by
    have heq : (y : ℂ) ^ w * f x y =
        ((y : ℂ) ^ (w + 1) * f x y) / (y : ℂ) := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy0.ne'), Complex.cpow_one]
      field_simp [Complex.ofReal_ne_zero.mpr hy0.ne']
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    exact div_le_div_of_nonneg_right (hb x y hy1) hy0.le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (fun x _ => hbound x)
  norm_num only [sub_neg_eq_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    abs_one, mul_one] at hi
  rw [dist_zero_right]
  simpa only [neg_div] using hi.trans_lt hCy

end RHTower.D4BMUniformCuspIntegration
