import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Cubic Taylor bounds for `arctan` and `sin`

Both `arctan` and `sin` agree with the identity to cubic order:

```text
|arctan u - u| ≤ |u|³,        |sin u - u| ≤ |u|³.
```

Each follows from the mean value inequality on the segment from `0` to `u`, where the derivative
of the difference is `-u²/(1+u²)` respectively `cos u - 1`, both bounded by `u²` in absolute
value.
-/

open Set

namespace HTGeometry

/-- The cubic Taylor bound for `arctan`. -/
theorem abs_arctan_sub_self_le (u : ℝ) : |Real.arctan u - u| ≤ |u| ^ 3 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) u,
      HasDerivWithinAt (fun y : ℝ => Real.arctan y - y) (1 / (1 + x ^ 2) - 1) (uIcc 0 u) x := by
    intro x _
    exact ((Real.hasDerivAt_arctan x).sub (hasDerivAt_id x)).hasDerivWithinAt
  have hbound : ∀ x ∈ uIcc (0 : ℝ) u, ‖1 / (1 + x ^ 2) - 1‖ ≤ |u| ^ 2 := by
    intro x hx
    have hden : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hval : 1 / (1 + x ^ 2) - 1 = -(x ^ 2 / (1 + x ^ 2)) := by
      field_simp
      ring
    have hle : x ^ 2 / (1 + x ^ 2) ≤ x ^ 2 := by
      rw [div_le_iff₀ hden]
      nlinarith [sq_nonneg x]
    have hxu : |x| ≤ |u| := by
      rcases le_total 0 u with hu | hu
      · rw [uIcc_of_le hu] at hx
        rw [abs_of_nonneg hx.1, abs_of_nonneg hu]
        exact hx.2
      · rw [uIcc_of_ge hu] at hx
        rw [abs_of_nonpos hx.2, abs_of_nonpos hu]
        linarith [hx.1]
    have hsq : x ^ 2 ≤ |u| ^ 2 := by
      have h1 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      rw [h1]
      exact pow_le_pow_left₀ (abs_nonneg x) hxu 2
    rw [hval, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    linarith
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc 0 u) (left_mem_uIcc) (right_mem_uIcc)
  simp only [Real.arctan_zero, sub_zero, Real.norm_eq_abs, sub_zero] at hmvt
  calc |Real.arctan u - u| ≤ |u| ^ 2 * |u| := hmvt
    _ = |u| ^ 3 := by ring

/-- The cubic Taylor bound for `sin`. -/
theorem abs_sin_sub_self_le (u : ℝ) : |Real.sin u - u| ≤ |u| ^ 3 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) u,
      HasDerivWithinAt (fun y : ℝ => Real.sin y - y) (Real.cos x - 1) (uIcc 0 u) x := by
    intro x _
    exact ((Real.hasDerivAt_sin x).sub (hasDerivAt_id x)).hasDerivWithinAt
  have hbound : ∀ x ∈ uIcc (0 : ℝ) u, ‖Real.cos x - 1‖ ≤ |u| ^ 2 := by
    intro x hx
    have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
    have hcos1 := Real.cos_le_one x
    have hxu : |x| ≤ |u| := by
      rcases le_total 0 u with hu | hu
      · rw [uIcc_of_le hu] at hx
        rw [abs_of_nonneg hx.1, abs_of_nonneg hu]
        exact hx.2
      · rw [uIcc_of_ge hu] at hx
        rw [abs_of_nonpos hx.2, abs_of_nonpos hu]
        linarith [hx.1]
    have hsq : x ^ 2 ≤ |u| ^ 2 := by
      have h1 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      rw [h1]
      exact pow_le_pow_left₀ (abs_nonneg x) hxu 2
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc 0 u) (left_mem_uIcc) (right_mem_uIcc)
  simp only [Real.sin_zero, sub_zero, Real.norm_eq_abs] at hmvt
  calc |Real.sin u - u| ≤ |u| ^ 2 * |u| := hmvt
    _ = |u| ^ 3 := by ring

end HTGeometry
