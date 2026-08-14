import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Artanh

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

/-- The quadratic Taylor bound for the logarithm on `|x| ≤ 1/2`. -/
theorem abs_log_one_add_sub_self_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hxabs : -(1 / 2 : ℝ) ≤ x ∧ x ≤ 1 / 2 := abs_le.mp hx
  have hmem : ∀ y ∈ uIcc (0 : ℝ) x, |y| ≤ |x| := by
    intro y hy
    rcases le_total 0 x with hx0 | hx0
    · rw [uIcc_of_le hx0] at hy
      rw [abs_of_nonneg hy.1, abs_of_nonneg hx0]
      exact hy.2
    · rw [uIcc_of_ge hx0] at hy
      rw [abs_of_nonpos hy.2, abs_of_nonpos hx0]
      linarith [hy.1]
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) x,
      HasDerivWithinAt (fun z : ℝ => Real.log (1 + z) - z) (1 / (1 + y) - 1) (uIcc 0 x) y := by
    intro y hy
    have hyabs := hmem y hy
    have hy1 : (0 : ℝ) < 1 + y := by
      have := abs_le.mp (le_trans hyabs hx)
      linarith [this.1]
    have hlog : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + y)) y := by
      have hbase : HasDerivAt (fun z : ℝ => 1 + z) 1 y := (hasDerivAt_id y).const_add (1 : ℝ)
      have h := (Real.hasDerivAt_log (ne_of_gt hy1)).comp y hbase
      simpa [one_div, Function.comp_def] using h
    exact (hlog.sub (hasDerivAt_id y)).hasDerivWithinAt
  have hbound : ∀ y ∈ uIcc (0 : ℝ) x, ‖1 / (1 + y) - 1‖ ≤ 2 * |x| := by
    intro y hy
    have hyabs := hmem y hy
    have hyle : |y| ≤ 1 / 2 := le_trans hyabs hx
    have hy2 := abs_le.mp hyle
    have hy1 : (1 : ℝ) / 2 ≤ 1 + y := by linarith [hy2.1]
    have hy1pos : (0 : ℝ) < 1 + y := by linarith
    have hval : 1 / (1 + y) - 1 = -(y / (1 + y)) := by
      rw [div_sub_one (ne_of_gt hy1pos), ← neg_div]
      congr 1
      ring
    have hle : |y| / (1 + y) ≤ 2 * |x| := by
      rw [div_le_iff₀ hy1pos]
      nlinarith [hyabs, abs_nonneg x,
        mul_nonneg (abs_nonneg x) (by linarith [hy2.1] : (0:ℝ) ≤ 1 + 2 * y)]
    rw [hval, Real.norm_eq_abs, abs_neg, abs_div, abs_of_pos hy1pos]
    exact hle
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc 0 x) (left_mem_uIcc) (right_mem_uIcc)
  simp only [add_zero, Real.log_one, sub_zero, Real.norm_eq_abs] at hmvt
  calc |Real.log (1 + x) - x| ≤ 2 * |x| * |x| := hmvt
    _ = 2 * x ^ 2 := by
        rw [show (2 : ℝ) * |x| * |x| = 2 * (|x| * |x|) by ring, abs_mul_abs_self]
        ring

/-- The quadratic Taylor bound for `artanh` on `|u| ≤ 1/2`. -/
theorem abs_artanh_sub_self_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.artanh u - u| ≤ 4 * u ^ 2 := by
  have huabs := abs_le.mp hu
  have hu1 : (0 : ℝ) < 1 + u := by linarith [huabs.1]
  have hu2 : (0 : ℝ) < 1 - u := by linarith [huabs.2]
  have hmem : u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [huabs.1], by linarith [huabs.2]⟩
  have hval : Real.artanh u = 1 / 2 * (Real.log (1 + u) - Real.log (1 - u)) := by
    rw [Real.artanh_eq_half_log hmem, Real.log_div (ne_of_gt hu1) (ne_of_gt hu2)]
  have hplus := abs_log_one_add_sub_self_le hu
  have hminus : |Real.log (1 - u) - (-u)| ≤ 2 * u ^ 2 := by
    have hneg : |(-u)| ≤ 1 / 2 := by rwa [abs_neg]
    have h := abs_log_one_add_sub_self_le hneg
    have hrw : (1 : ℝ) + -u = 1 - u := by ring
    rw [hrw] at h
    have hsq : (-u) ^ 2 = u ^ 2 := by ring
    rw [hsq] at h
    exact h
  have hdiff : Real.artanh u - u
      = 1 / 2 * ((Real.log (1 + u) - u) - (Real.log (1 - u) - (-u))) := by
    rw [hval]
    ring
  have hkey : |Real.log (1 + u) - u - (Real.log (1 - u) - -u)| ≤ 4 * u ^ 2 := by
    calc |Real.log (1 + u) - u - (Real.log (1 - u) - -u)|
        ≤ |Real.log (1 + u) - u| + |Real.log (1 - u) - -u| := abs_sub _ _
      _ ≤ 2 * u ^ 2 + 2 * u ^ 2 := by linarith
      _ = 4 * u ^ 2 := by ring
  rw [hdiff, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  linarith [hkey, sq_nonneg u]

end HTGeometry
