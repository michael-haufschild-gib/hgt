import GaloisForLFunctions.RHTower.SmoothAFEGaussianResidue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Reciprocal contour term for the Gaussian Mellin residue

The Gaussian Mellin integrand has unit principal part `1 / w`.  This module evaluates its
symmetric finite vertical integrals by elementary real calculus:

* on a positive vertical line they tend to `π`;
* on a negative vertical line they tend to `-π`;
* the two horizontal reciprocal integrals tend to zero.

These are the explicit residue terms needed to shift the Gaussian Mellin contour through zero.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RHTower

theorem vertical_inv_pointwise {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    (((σ : ℂ) + (t : ℂ) * I)⁻¹)
      = (σ / (σ ^ 2 + t ^ 2) : ℝ)
        - (t / (σ ^ 2 + t ^ 2) : ℝ) * I := by
  have hden : σ ^ 2 + t ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hσ, sq_nonneg t]
  rw [Complex.inv_def]
  simp [Complex.normSq_apply, div_eq_mul_inv]
  ring

theorem integral_odd_div_sq_add_sq {σ T : ℝ} :
    (∫ t : ℝ in (-T)..T, t / (σ ^ 2 + t ^ 2)) = 0 := by
  let f : ℝ → ℝ := fun t => t / (σ ^ 2 + t ^ 2)
  have hodd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    dsimp [f]
    ring
  have hcomp := intervalIntegral.integral_comp_neg (f := f)
    (a := -T) (b := T)
  have heq : (∫ t : ℝ in (-T)..T, f (-t)) = ∫ t : ℝ in (-T)..T, f t := by
    simp only [neg_neg] at hcomp
    exact hcomp
  rw [show (fun t => f (-t)) = fun t => -f t by funext t; exact hodd t,
    intervalIntegral.integral_neg] at heq
  exact neg_eq_self.mp heq

theorem integral_vertical_inv {σ T : ℝ} (hσ : σ ≠ 0) :
    (∫ t : ℝ in (-T)..T, (((σ : ℂ) + (t : ℂ) * I)⁻¹))
      = (Real.arctan (T / σ) - Real.arctan (-T / σ) : ℝ) := by
  have hden : ∀ t : ℝ, σ ^ 2 + t ^ 2 ≠ 0 := fun t => by
    nlinarith [sq_pos_of_ne_zero hσ, sq_nonneg t]
  have hc1 : Continuous (fun t : ℝ => σ / (σ ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) hden
  have hc2 : Continuous (fun t : ℝ => t / (σ ^ 2 + t ^ 2)) :=
    continuous_id.div (by fun_prop) hden
  have hi1 : IntervalIntegrable
      (fun t : ℝ => ((σ / (σ ^ 2 + t ^ 2) : ℝ) : ℂ)) volume (-T) T := by
    exact (Complex.continuous_ofReal.comp hc1).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun t : ℝ => ((t / (σ ^ 2 + t ^ 2) : ℝ) : ℂ) * I) volume (-T) T :=
    ((Complex.continuous_ofReal.comp hc2).mul
      (continuous_const : Continuous (fun _ : ℝ => I))).intervalIntegrable _ _
  simp_rw [vertical_inv_pointwise hσ]
  rw [intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_odd_div_sq_add_sq, ofReal_zero, zero_mul, sub_zero]
  norm_cast
  exact integral_div_sq_add_sq

theorem tendsto_integral_vertical_inv_of_pos {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun T : ℝ =>
      ∫ t : ℝ in (-T)..T, (((σ : ℂ) + (t : ℂ) * I)⁻¹))
      atTop (𝓝 (Real.pi : ℂ)) := by
  have harg : Tendsto (fun T : ℝ => T / σ) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hσ).2 tendsto_id
  have hatan : Tendsto (fun T : ℝ => Real.arctan (T / σ)) atTop
      (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg
  have htwo : Tendsto (fun T : ℝ => 2 * Real.arctan (T / σ)) atTop
      (𝓝 Real.pi) := by
    convert hatan.const_mul 2 using 1
    all_goals ring_nf
  convert (Complex.continuous_ofReal.tendsto _).comp htwo using 1
  · funext T
    rw [integral_vertical_inv hσ.ne', show -T / σ = -(T / σ) by ring,
      Real.arctan_neg]
    simp [Function.comp_apply]
    ring

theorem tendsto_integral_vertical_inv_of_neg {σ : ℝ} (hσ : σ < 0) :
    Tendsto (fun T : ℝ =>
      ∫ t : ℝ in (-T)..T, (((σ : ℂ) + (t : ℂ) * I)⁻¹))
      atTop (𝓝 (-(Real.pi : ℂ))) := by
  have harg : Tendsto (fun T : ℝ => T / σ) atTop atBot :=
    (tendsto_div_const_atBot_of_neg hσ).2 tendsto_id
  have hatan : Tendsto (fun T : ℝ => Real.arctan (T / σ)) atTop
      (𝓝 (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp harg
  have htwo : Tendsto (fun T : ℝ => 2 * Real.arctan (T / σ)) atTop
      (𝓝 (-Real.pi)) := by
    convert hatan.const_mul 2 using 1
    all_goals ring_nf
  convert (Complex.continuous_ofReal.tendsto _).comp htwo using 1
  · funext T
    rw [integral_vertical_inv hσ.ne, show -T / σ = -(T / σ) by ring,
      Real.arctan_neg]
    simp [Function.comp_apply]
    ring
  · simp

theorem tendsto_integral_horizontal_inv (a b : ℝ) :
    Tendsto (fun T : ℝ =>
      ∫ u : ℝ in a..b, (((u : ℂ) + (T : ℂ) * I)⁻¹))
      atTop (𝓝 0) := by
  have hmajor : Tendsto (fun T : ℝ => |b - a| / T) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop |b - a|
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hbd : ∀ u ∈ Set.uIoc a b,
      ‖(((u : ℂ) + (T : ℂ) * I)⁻¹)‖ ≤ 1 / T := by
    intro u _
    have hden : T ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := by
      calc
        T = |(((u : ℂ) + (T : ℂ) * I)).im| := by simp [abs_of_pos hT]
        _ ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := Complex.abs_im_le_norm _
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hT hden
  calc
    ‖∫ u : ℝ in a..b, (((u : ℂ) + (T : ℂ) * I)⁻¹)‖
        ≤ (1 / T) * |b - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = |b - a| / T := by ring

theorem tendsto_integral_horizontal_inv_neg (a b : ℝ) :
    Tendsto (fun T : ℝ =>
      ∫ u : ℝ in a..b, (((u : ℂ) - (T : ℂ) * I)⁻¹))
      atTop (𝓝 0) := by
  have hmajor : Tendsto (fun T : ℝ => |b - a| / T) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop |b - a|
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hbd : ∀ u ∈ Set.uIoc a b,
      ‖(((u : ℂ) - (T : ℂ) * I)⁻¹)‖ ≤ 1 / T := by
    intro u _
    have hden : T ≤ ‖(u : ℂ) - (T : ℂ) * I‖ := by
      calc
        T = |(((u : ℂ) - (T : ℂ) * I)).im| := by simp [abs_of_pos hT]
        _ ≤ ‖(u : ℂ) - (T : ℂ) * I‖ := Complex.abs_im_le_norm _
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hT hden
  calc
    ‖∫ u : ℝ in a..b, (((u : ℂ) - (T : ℂ) * I)⁻¹)‖
        ≤ (1 / T) * |b - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = |b - a| / T := by ring

end RHTower
