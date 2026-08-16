import Mathlib

/-!
# The shape ratio under dilation and rescaling

For a profile `f` and its dilated, rescaled copy `g(x) = β f(x/α)`, the two integrals over matching
windows scale as

```text
∫_{-αR}^{αR} g = α β ∫_{-R}^{R} f ,        ∫_{-αR}^{αR} g² = α β² ∫_{-R}^{R} f² ,
```

so the *shape ratio* picks up exactly one factor of the dilation and none of the amplitude:

```text
( ∫_{-αR}^{αR} g )² / ∫_{-αR}^{αR} g²  =  α · ( ∫_{-R}^{R} f )² / ∫_{-R}^{R} f² .
```

The amplitude drops out because the numerator is quadratic and the denominator is quadratic; the
dilation survives once because the numerator is squared after integrating.  This is the invariance
that lets a limit computed in one normalisation of an eigenfunction family be transported to
another: only the dilation factor has to be tracked.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- The first moment of a dilated, rescaled profile over the matching window. -/
theorem intervalIntegral_dilate (f : ℝ → ℝ) {α : ℝ} (hα : α ≠ 0) (β R : ℝ) :
    (∫ x in -(α * R)..(α * R), β * f (x / α)) = α * β * ∫ x in -R..R, f x := by
  have hdiv := intervalIntegral.integral_comp_div (a := -(α * R)) (b := α * R) f hα
  have hleft : -(α * R) / α = -R := by field_simp
  have hright : (α * R) / α = R := by field_simp
  rw [hleft, hright] at hdiv
  rw [intervalIntegral.integral_const_mul, hdiv, smul_eq_mul]
  ring

/-- The second moment of a dilated, rescaled profile over the matching window. -/
theorem intervalIntegral_dilate_sq (f : ℝ → ℝ) {α : ℝ} (hα : α ≠ 0) (β R : ℝ) :
    (∫ x in -(α * R)..(α * R), (β * f (x / α)) ^ 2)
      = α * β ^ 2 * ∫ x in -R..R, (f x) ^ 2 := by
  have hdiv := intervalIntegral.integral_comp_div (a := -(α * R)) (b := α * R)
    (fun u : ℝ => (f u) ^ 2) hα
  have hleft : -(α * R) / α = -R := by field_simp
  have hright : (α * R) / α = R := by field_simp
  rw [hleft, hright] at hdiv
  have hcongr : (∫ x in -(α * R)..(α * R), (β * f (x / α)) ^ 2)
      = ∫ x in -(α * R)..(α * R), β ^ 2 * (fun u : ℝ => (f u) ^ 2) (x / α) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, hdiv, smul_eq_mul]
  ring

/-- **The shape ratio scales by the dilation and ignores the amplitude.** -/
theorem shapeRatio_dilate (f : ℝ → ℝ) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (R : ℝ) :
    (∫ x in -(α * R)..(α * R), β * f (x / α)) ^ 2
        / (∫ x in -(α * R)..(α * R), (β * f (x / α)) ^ 2)
      = α * ((∫ x in -R..R, f x) ^ 2 / ∫ x in -R..R, (f x) ^ 2) := by
  rw [intervalIntegral_dilate f hα β R, intervalIntegral_dilate_sq f hα β R]
  rcases eq_or_ne (∫ x in -R..R, (f x) ^ 2) 0 with h | h
  · rw [h]
    simp
  · field_simp

/-- **The shape ratio is independent of the amplitude.** -/
theorem shapeRatio_amplitude_invariant (f : ℝ → ℝ) {β : ℝ} (hβ : β ≠ 0) (R : ℝ) :
    (∫ x in -R..R, β * f x) ^ 2 / (∫ x in -R..R, (β * f x) ^ 2)
      = (∫ x in -R..R, f x) ^ 2 / ∫ x in -R..R, (f x) ^ 2 := by
  have h := shapeRatio_dilate f (α := 1) one_ne_zero hβ R
  simpa using h

end GaloisForLFunctions.HTGeometry

end
