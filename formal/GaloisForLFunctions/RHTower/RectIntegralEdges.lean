import GaloisForLFunctions.RHTower.RectangleResidue
import GaloisForLFunctions.RHTower.LogModulusHorizontal
import GaloisForLFunctions.RHTower.LayerCakeZeroCount

/-!
# The imaginary part of a rectangle contour integral, edge by edge

`rectIntegral g z₁ z₂` is `(bottom − top) + i·right − i·left`.  Since `Im(i·w) = Re w`, taking
imaginary parts exchanges the roles of the two directions:

```text
Im (rectIntegral g z₁ z₂)
   =  ∫ Im g  along the bottom   −  ∫ Im g  along the top
    + ∫ Re g  along the right    −  ∫ Re g  along the left .
```

Applied to `g = f′/f`, the left-hand side is `2π` times the enclosed zero count (argument principle),
the vertical terms are integrals of `Re(f′/f)` — which by `integral_re_logDeriv_horizontal` integrate
in the abscissa to increments of `log‖f‖` — and the horizontal terms are the error.  This is the edge
decomposition Littlewood's lemma is assembled from, and it involves no branch of the logarithm.
-/

open Complex MeasureTheory intervalIntegral

namespace RHTower

/-- Interval integration commutes with taking imaginary parts. -/
theorem integral_im_eq {f : ℝ → ℂ} {a b : ℝ} (h : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x).im = ∫ x in a..b, (f x).im :=
  (Complex.imCLM.intervalIntegral_comp_comm h).symm

/-- Interval integration commutes with taking real parts. -/
theorem integral_re_eq {f : ℝ → ℂ} {a b : ℝ} (h : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x).re = ∫ x in a..b, (f x).re :=
  (Complex.reCLM.intervalIntegral_comp_comm h).symm

/-- **Edge decomposition of the imaginary part of a rectangle contour integral.**  The horizontal
edges contribute the imaginary part of `g`, the vertical edges its real part. -/
theorem im_rectIntegral (g : ℂ → ℂ) (z₁ z₂ : ℂ)
    (hbot : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + z₁.im * I)) volume z₁.re z₂.re)
    (htop : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + z₂.im * I)) volume z₁.re z₂.re)
    (hright : IntervalIntegrable (fun y : ℝ => g ((z₂.re : ℂ) + y * I)) volume z₁.im z₂.im)
    (hleft : IntervalIntegrable (fun y : ℝ => g ((z₁.re : ℂ) + y * I)) volume z₁.im z₂.im) :
    (rectIntegral g z₁ z₂).im
      = (∫ x in z₁.re..z₂.re, (g ((x : ℂ) + z₁.im * I)).im)
        - (∫ x in z₁.re..z₂.re, (g ((x : ℂ) + z₂.im * I)).im)
        + (∫ y in z₁.im..z₂.im, (g ((z₂.re : ℂ) + y * I)).re)
        - ∫ y in z₁.im..z₂.im, (g ((z₁.re : ℂ) + y * I)).re := by
  unfold rectIntegral
  simp only [Complex.sub_im, Complex.add_im, smul_eq_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add]
  rw [integral_im_eq hbot, integral_im_eq htop, integral_re_eq hright, integral_re_eq hleft]

/-- **The argument principle in edge form.**  If the rectangle integral of `logDeriv f` equals
`2πi·n`, its imaginary part gives `2πn` as a sum of four real edge integrals: the horizontals in
`Im (f′/f)` and the verticals in `Re (f′/f)`. -/
theorem two_pi_mul_count_eq_edges {f : ℂ → ℂ} {z₁ z₂ : ℂ} {n : ℝ}
    (hval : rectIntegral (logDeriv f) z₁ z₂ = 2 * Real.pi * I * (n : ℂ))
    (hbot : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + z₁.im * I)) volume z₁.re z₂.re)
    (htop : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + z₂.im * I)) volume z₁.re z₂.re)
    (hright : IntervalIntegrable (fun y : ℝ => logDeriv f ((z₂.re : ℂ) + y * I)) volume z₁.im z₂.im)
    (hleft : IntervalIntegrable (fun y : ℝ => logDeriv f ((z₁.re : ℂ) + y * I)) volume z₁.im z₂.im) :
    2 * Real.pi * n
      = (∫ x in z₁.re..z₂.re, (logDeriv f ((x : ℂ) + z₁.im * I)).im)
        - (∫ x in z₁.re..z₂.re, (logDeriv f ((x : ℂ) + z₂.im * I)).im)
        + (∫ y in z₁.im..z₂.im, (logDeriv f ((z₂.re : ℂ) + y * I)).re)
        - ∫ y in z₁.im..z₂.im, (logDeriv f ((z₁.re : ℂ) + y * I)).re := by
  rw [← im_rectIntegral (logDeriv f) z₁ z₂ hbot htop hright hleft, hval]
  simp [Complex.mul_im]


/-! ### Assembling Littlewood's lemma

Integrating the edge identity in the abscissa and applying `sum_sub_eq_integral_count` on the left,
the left-edge term becomes — by Fubini and `integral_re_logDeriv_horizontal` — the pair of
log-modulus integrals.  Fubini and the integrability of the counting function are stated as
hypotheses; everything else is proved. -/

/-- **Littlewood's lemma from the edge identity.**  With `N σ` the count of abscissas exceeding `σ`,
the edge identity holding at every `σ`, and the left-edge term integrating (Fubini) to the
log-modulus pair, the weighted zero sum is given by the boundary data. -/
theorem littlewood_from_edges {σ₀ σ₁ : ℝ} {Z : Finset ℝ}
    {Bot Top Right Left : ℝ → ℝ} {logPair : ℝ}
    (hZ : ∀ b ∈ Z, σ₀ ≤ b ∧ b ≤ σ₁)
    (hedges : ∀ σ, 2 * Real.pi * ((Z.filter fun b => σ < b).card : ℝ)
      = Bot σ - Top σ + Right σ - Left σ)
    (hBTR : IntervalIntegrable (fun σ => Bot σ - Top σ + Right σ) volume σ₀ σ₁)
    (hLeft : IntervalIntegrable Left volume σ₀ σ₁)
    (hfub : (∫ σ in σ₀..σ₁, Left σ) = logPair) :
    2 * Real.pi * (∑ b ∈ Z, (b - σ₀))
      = (∫ σ in σ₀..σ₁, (Bot σ - Top σ + Right σ)) - logPair := by
  have hcake := sum_sub_eq_integral_count (σ₀ := σ₀) (σ₁ := σ₁) Z hZ
  have hpush : 2 * Real.pi * (∑ b ∈ Z, (b - σ₀))
      = ∫ σ in σ₀..σ₁, 2 * Real.pi * ((Z.filter fun b => σ < b).card : ℝ) := by
    rw [intervalIntegral.integral_const_mul, ← hcake]
  rw [hpush]
  have hcongr : (∫ σ in σ₀..σ₁, 2 * Real.pi * ((Z.filter fun b => σ < b).card : ℝ))
      = ∫ σ in σ₀..σ₁, ((Bot σ - Top σ + Right σ) - Left σ) := by
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [hedges σ]
  rw [hcongr, intervalIntegral.integral_sub hBTR hLeft, hfub]


end RHTower
