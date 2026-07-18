import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The multiplicative gauge chart

Perturbing an exponential density multiplicatively is what makes the Herglotz jet map affine: the
density `exp u₀` is replaced by `exp u₀ * (1 + h)`, which is again an exponential density, with
parameter `u₀ + log (1 + h)`.

For this to be a small perturbation of the parameter one needs the elementary bound

```text
|log (1 + x)| ≤ 2 |x|    for |x| ≤ 1 / 2,
```

so a uniformly small multiplicative gauge is a uniformly small additive change of parameter.  The
upper half follows from `log y ≤ y - 1`; the lower half from `exp (2x) ≤ 1 / (1 - 2x) ≤ 1 + x`,
which holds exactly on the stated range.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- On the range where the multiplicative gauge is at most one half, the density stays positive. -/
theorem one_add_pos_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) : 0 < 1 + x := by
  have h := neg_le_of_abs_le hx
  linarith

/-- The exponential lower bound underlying the logarithmic gauge estimate. -/
theorem exp_two_mul_le_one_add {x : ℝ} (hx : |x| ≤ 1 / 2) (hneg : x ≤ 0) :
    Real.exp (2 * x) ≤ 1 + x := by
  have hxlow : -(1 / 2) ≤ x := neg_le_of_abs_le hx
  have hden : 0 < 1 - 2 * x := by linarith
  have hE : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hexp : 1 - 2 * x ≤ Real.exp (-(2 * x)) := by
    have := Real.add_one_le_exp (-(2 * x))
    linarith
  have h1 : 1 - 2 * x ≤ (Real.exp (2 * x))⁻¹ := by
    rwa [Real.exp_neg] at hexp
  have h2 : Real.exp (2 * x) * (1 - 2 * x) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hE)
    rwa [mul_inv_cancel₀ (ne_of_gt hE)] at hmul
  have hstep : Real.exp (2 * x) ≤ (1 - 2 * x)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hden]
    exact h2
  refine le_trans hstep ?_
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith [hxlow, hneg]

/-- **The logarithmic gauge estimate.**  A multiplicative gauge of size at most one half changes
the exponential parameter by at most twice its size. -/
theorem abs_log_one_add_le_two_mul {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x)| ≤ 2 * |x| := by
  have hpos : 0 < 1 + x := one_add_pos_of_abs_le_half hx
  rw [abs_le]
  constructor
  · by_cases hneg : x ≤ 0
    · have hlow : 2 * x ≤ Real.log (1 + x) := by
        rw [Real.le_log_iff_exp_le hpos]
        exact exp_two_mul_le_one_add hx hneg
      have habs : |x| = -x := abs_of_nonpos hneg
      rw [habs]
      linarith
    · have hnonneg : 0 < x := by linarith [not_le.mp hneg]
      have hlog : 0 ≤ Real.log (1 + x) := by
        apply Real.log_nonneg
        linarith
      have habs : |x| = x := abs_of_pos hnonneg
      rw [habs]
      linarith
  · have hupper : Real.log (1 + x) ≤ x := by
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    have hxle : x ≤ |x| := le_abs_self x
    have hnn : 0 ≤ |x| := abs_nonneg x
    linarith

/-- Reparameterizing a multiplicative gauge as an additive change of the exponential parameter. -/
theorem exp_add_log_one_add {u x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.exp (u + Real.log (1 + x)) = Real.exp u * (1 + x) := by
  rw [Real.exp_add, Real.exp_log (one_add_pos_of_abs_le_half hx)]

end

end GaloisForLFunctions.HTGeometry
