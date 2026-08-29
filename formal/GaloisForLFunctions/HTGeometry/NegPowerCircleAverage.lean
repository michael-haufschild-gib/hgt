import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle averages of negative powers of the distance to a point

For `0 < α < 1` the average of `‖r e^{iθ} − u‖^{-α}` over the circle of radius `r` is at most a
constant multiple of `r^{-α}`, *uniformly in the point `u`*.  The mechanism is the elementary
inequality

```text
‖r e^{iθ} − u‖ ≥ r · |sin(θ − arg u)|,
```

which says that the distance from a point of the circle to `u` is at least its distance to the line
through `0` and `u`, together with the integrability of `|sin|^{-α}`.

This uniform bound is what makes the sum over an entire divisor affordable in Nevanlinna's estimate
for the proximity of a logarithmic derivative: each of the `n(R)` divisor terms costs a fixed
constant in the `α`-th power average, so the resulting logarithm costs only `log n(R)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Real MeasureTheory intervalIntegral

/-! ## Integrability of a negative power of `|sin|` -/

theorem measurable_abs_sin_rpow_neg (α : ℝ) :
    Measurable fun θ : ℝ => |Real.sin θ| ^ (-α) :=
  (Real.continuous_sin.abs.measurable).pow_const _

/-- On `[0, π/2]` the negative power of `|sin|` is dominated by the same power of the argument. -/
theorem abs_sin_rpow_neg_le_of_mem_left {α : ℝ} (hα0 : 0 < α) {θ : ℝ}
    (h0 : 0 < θ) (h1 : θ ≤ π / 2) :
    |Real.sin θ| ^ (-α) ≤ (2 / π) ^ (-α) * θ ^ (-α) := by
  have hπ : 0 < π := Real.pi_pos
  have hlow : 2 / π * θ ≤ Real.sin θ := Real.mul_le_sin h0.le h1
  have hpos : 0 < 2 / π * θ := by positivity
  have hsin : 0 < Real.sin θ := lt_of_lt_of_le hpos hlow
  have habs : |Real.sin θ| = Real.sin θ := abs_of_pos hsin
  rw [habs]
  have hstep : Real.sin θ ^ (-α) ≤ (2 / π * θ) ^ (-α) := by
    refine Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
  calc Real.sin θ ^ (-α) ≤ (2 / π * θ) ^ (-α) := hstep
    _ = (2 / π) ^ (-α) * θ ^ (-α) := by
        rw [Real.mul_rpow (by positivity) h0.le]

theorem intervalIntegrable_abs_sin_rpow_neg_left {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume 0 (π / 2) := by
  have hπ : 0 < π := Real.pi_pos
  have hdom : IntervalIntegrable (fun θ : ℝ => (2 / π) ^ (-α) * θ ^ (-α)) volume 0 (π / 2) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  refine IntervalIntegrable.mono_fun' hdom
    ((measurable_abs_sin_rpow_neg α).aestronglyMeasurable.restrict) ?_
  have hae : ∀ᵐ θ : ℝ ∂(volume.restrict (Set.uIoc 0 (π / 2))),
      ‖|Real.sin θ| ^ (-α)‖ ≤ (2 / π) ^ (-α) * θ ^ (-α) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun θ hθ => ?_
    rw [Set.uIoc_of_le (by positivity)] at hθ
    have h0 : 0 < θ := hθ.1
    have h1 : θ ≤ π / 2 := hθ.2
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact abs_sin_rpow_neg_le_of_mem_left hα0 h0 h1
  exact hae

theorem intervalIntegrable_abs_sin_rpow_neg_right {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume (π / 2) π := by
  have hbase := intervalIntegrable_abs_sin_rpow_neg_left hα0 hα1
  have hcomp := hbase.comp_sub_left π
  have hfun : (fun θ : ℝ => |Real.sin (π - θ)| ^ (-α)) = fun θ : ℝ => |Real.sin θ| ^ (-α) := by
    funext θ
    rw [Real.sin_pi_sub]
  rw [hfun] at hcomp
  have hleft : π - π / 2 = π / 2 := by ring
  have hright : π - 0 = π := by ring
  rw [hleft, hright] at hcomp
  exact hcomp.symm

theorem intervalIntegrable_abs_sin_rpow_neg_pi {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume 0 π :=
  (intervalIntegrable_abs_sin_rpow_neg_left hα0 hα1).trans
    (intervalIntegrable_abs_sin_rpow_neg_right hα0 hα1)

theorem intervalIntegrable_abs_sin_rpow_neg_two_pi {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume 0 (2 * π) := by
  have hbase := intervalIntegrable_abs_sin_rpow_neg_pi hα0 hα1
  have hcomp := hbase.comp_sub_right π
  have hfun : (fun θ : ℝ => |Real.sin (θ - π)| ^ (-α)) = fun θ : ℝ => |Real.sin θ| ^ (-α) := by
    funext θ
    rw [Real.sin_sub_pi, abs_neg]
  rw [hfun] at hcomp
  have hleft : (0 : ℝ) + π = π := by ring
  have hright : π + π = 2 * π := by ring
  rw [hleft, hright] at hcomp
  exact hbase.trans hcomp

/-- The finite constant `∫_0^{2π} |sin θ|^{-α} dθ`. -/
noncomputable def sinNegPowerConst (α : ℝ) : ℝ := ∫ θ in (0 : ℝ)..(2 * π), |Real.sin θ| ^ (-α)

theorem sinNegPowerConst_nonneg (α : ℝ) : 0 ≤ sinNegPowerConst α := by
  rw [sinNegPowerConst]
  refine intervalIntegral.integral_nonneg (by positivity) fun θ _ => ?_
  positivity

/-- The `|sin|` integral is translation invariant: `|sin|` is `π`-periodic, hence `2π`-periodic. -/
theorem integral_abs_sin_rpow_neg_shift {α : ℝ} (φ : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), |Real.sin (θ - φ)| ^ (-α) = sinNegPowerConst α := by
  have hper : Function.Periodic (fun θ : ℝ => |Real.sin θ| ^ (-α)) (2 * π) := fun θ => by
    show |Real.sin (θ + 2 * π)| ^ (-α) = |Real.sin θ| ^ (-α)
    rw [Real.sin_add_two_pi]
  rw [intervalIntegral.integral_comp_sub_right (fun θ => |Real.sin θ| ^ (-α)) φ]
  have h := Function.Periodic.intervalIntegral_add_eq hper (0 - φ) 0
  rw [sinNegPowerConst, show (2 : ℝ) * π - φ = 0 - φ + 2 * π by ring, h]
  norm_num

/-! ## The geometric lower bound on the circle -/

/-- **The distance from a circle point to `u` is at least its distance to the line through `u`.** -/
theorem norm_circle_sub_ge (r : ℝ) (hr : 0 ≤ r) (u : ℂ) (θ : ℝ) :
    r * |Real.sin (θ - u.arg)| ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ := by
  set φ : ℝ := u.arg with hφ
  set ρ : ℝ := ‖u‖ with hρ
  have hu : (ρ : ℂ) * Complex.exp ((φ : ℝ) * Complex.I) = u := Complex.norm_mul_exp_arg_mul_I u
  have hexp : Complex.exp ((φ : ℝ) * Complex.I) * Complex.exp (((θ - φ : ℝ)) * Complex.I)
      = Complex.exp ((θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hrot : (r : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) - u
      = Complex.exp ((φ : ℝ) * Complex.I)
        * ((r : ℂ) * Complex.exp (((θ - φ : ℝ)) * Complex.I) - (ρ : ℂ)) := by
    rw [← hu, mul_sub]
    rw [show Complex.exp ((φ : ℝ) * Complex.I) * ((r : ℂ) * Complex.exp (((θ - φ : ℝ)) * Complex.I))
        = (r : ℂ) * (Complex.exp ((φ : ℝ) * Complex.I)
          * Complex.exp (((θ - φ : ℝ)) * Complex.I)) from by ring]
    rw [hexp]
    ring
  have hre : (((φ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  have him : ((r : ℂ) * Complex.exp (((θ - φ : ℝ)) * Complex.I) - (ρ : ℂ)).im
      = r * Real.sin (θ - φ) := by
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
  have hle := Complex.abs_im_le_norm
    ((r : ℂ) * Complex.exp (((θ - φ : ℝ)) * Complex.I) - (ρ : ℂ))
  rw [him] at hle
  rw [hrot, norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul]
  calc r * |Real.sin (θ - φ)| = |r * Real.sin (θ - φ)| := by
        rw [abs_mul, abs_of_nonneg hr]
    _ ≤ _ := hle

end GaloisForLFunctions.HTGeometry
