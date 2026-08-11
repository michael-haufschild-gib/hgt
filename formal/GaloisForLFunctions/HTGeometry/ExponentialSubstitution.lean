import Mathlib

/-!
# The exponential change of variables

The half-line source of the polar estimate lives in the logarithmic variable and the radial mode
lives in the multiplicative one.  The substitution `x = exp s` converts between them:

```text
∫_0^t exp(s/2) f(exp s) ds = ∫_1^{exp t} f(x) x^{-1/2} dx.
```

The weight `exp(s/2)` on the left is exactly `dx/√x` on the right, which is why the growing branch
of the autocorrelation and the `x^{-1/2}`-weighted radial primitive are the same object.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace HTGeometry

theorem sqrt_exp' (s : ℝ) : Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
  have h : Real.exp s = Real.exp (s / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [h, Real.sqrt_sq (Real.exp_pos _).le]

theorem exp_image_subset_Icc {t : ℝ} (ht : 0 ≤ t) :
    Real.exp '' Set.uIcc (0 : ℝ) t ⊆ Set.Icc 1 (Real.exp t) := by
  rintro y ⟨x, hx, rfl⟩
  rw [Set.uIcc_of_le ht] at hx
  constructor
  · calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx.1
  · exact Real.exp_le_exp.mpr hx.2

/-- **The exponential substitution.**  The logarithmic half-line primitive with weight `exp(s/2)`
is the multiplicative primitive with weight `x^{-1/2}`. -/
theorem integral_exp_half_comp_exp (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hf : ContinuousOn f (Set.Icc 1 (Real.exp t))) :
    (∫ s in (0 : ℝ)..t, Real.exp (s / 2) * f (Real.exp s))
      = ∫ x in (1 : ℝ)..Real.exp t, f x / Real.sqrt x := by
  have hg : ContinuousOn (fun x : ℝ => f x / Real.sqrt x)
      (Real.exp '' Set.uIcc (0 : ℝ) t) := by
    refine ContinuousOn.div (hf.mono (exp_image_subset_Icc ht))
      (Real.continuous_sqrt.continuousOn) ?_
    rintro y ⟨x, _, rfl⟩
    exact ne_of_gt (Real.sqrt_pos.mpr (Real.exp_pos x))
  have hmain := intervalIntegral.integral_deriv_smul_comp'
    (f := Real.exp) (f' := Real.exp) (g := fun x : ℝ => f x / Real.sqrt x)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hg
  rw [Real.exp_zero] at hmain
  rw [← hmain]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  simp only [Function.comp_apply, smul_eq_mul]
  rw [sqrt_exp']
  have hne : Real.exp (s / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp
  have hsq : Real.exp (s / 2) ^ 2 = Real.exp s := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hsq]
  ring

end HTGeometry
