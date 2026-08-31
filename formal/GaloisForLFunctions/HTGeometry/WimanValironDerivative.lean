import Mathlib

/-!
# Reading the Wiman–Valiron estimate on the derivative

The estimate is stated as a bound on `z F′(z)/F(z) − ν`.  Since `‖z F′/F‖ = r ‖F′‖ / ‖F‖`, a relative
bound `≤ ε ν` on that difference is exactly a two-sided bound

```text
(1 − ε) ν ‖F(z)‖ / r  ≤  ‖F′(z)‖  ≤  (1 + ε) ν ‖F(z)‖ / r,
```

which is the form an algebraic relation in `F` and `F′` consumes: it converts a Newton-polygon
comparison between `‖F′‖` and a power of `‖F‖` into a comparison between `ν/r` and that power.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The Wiman–Valiron estimate, read on the derivative.**  A relative bound on
`z F′(z)/F(z) − ν` becomes a two-sided bound on `‖F′(z)‖` in terms of `ν ‖F(z)‖ / r`. -/
theorem norm_deriv_between_of_wv {F : ℂ → ℂ} {z : ℂ} {r nu eps : ℝ}
    (hz : ‖z‖ = r) (hr : 0 < r) (hnu : 0 ≤ nu) (hF : F z ≠ 0)
    (hwv : ‖z * deriv F z / F z - (nu : ℂ)‖ ≤ eps * nu) :
    (1 - eps) * nu * ‖F z‖ / r ≤ ‖deriv F z‖
      ∧ ‖deriv F z‖ ≤ (1 + eps) * nu * ‖F z‖ / r := by
  have hFn : 0 < ‖F z‖ := norm_pos_iff.mpr hF
  have hnorm : ‖z * deriv F z / F z‖ = r * ‖deriv F z‖ / ‖F z‖ := by
    rw [norm_div, norm_mul, hz]
  have hcast : ‖((nu : ℝ) : ℂ)‖ = nu := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnu]
  have hlow : nu - eps * nu ≤ ‖z * deriv F z / F z‖ := by
    have h := norm_sub_norm_le ((nu : ℝ) : ℂ) (z * deriv F z / F z)
    rw [norm_sub_rev, hcast] at h
    linarith [h, hwv]
  have hhigh : ‖z * deriv F z / F z‖ ≤ nu + eps * nu := by
    have h : ‖z * deriv F z / F z‖
        ≤ ‖z * deriv F z / F z - ((nu : ℝ) : ℂ)‖ + ‖((nu : ℝ) : ℂ)‖ := by
      simpa using norm_add_le (z * deriv F z / F z - ((nu : ℝ) : ℂ)) ((nu : ℝ) : ℂ)
    rw [hcast] at h
    linarith [h, hwv]
  rw [hnorm] at hlow hhigh
  constructor
  · rw [div_le_iff₀ hr]
    rw [le_div_iff₀ hFn] at hlow
    nlinarith [hlow, hFn, hr]
  · rw [le_div_iff₀ hr]
    rw [div_le_iff₀ hFn] at hhigh
    nlinarith [hhigh, hFn, hr]

end GaloisForLFunctions.HTGeometry
