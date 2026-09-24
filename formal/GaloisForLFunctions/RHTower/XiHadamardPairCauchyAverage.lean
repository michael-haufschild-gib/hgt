import GaloisForLFunctions.RHTower.XiHadamardPairOrdinateIntegral

/-!
# Ordinate averaging is abscissa translation

Two Cauchy kernels of widths `a` and `h` have ordinate product integrating to the single kernel of
width `a + h`:

```text
∫_ℝ (a/(a²+y²)) (h/(h²+y²)) dy = π/(a+h) .
```

Consequently a line-conjugate pair averaged against a Cauchy weight of width `h` is `π` times the
same pair at abscissa shifted right by `h`.  Averaging in the ordinate therefore produces nothing
the pointwise statement does not already carry: it re-evaluates the criterion further from the
critical line, where it is weaker.  This is the exact reason averaging arguments cannot separate an
off-line zero from its absence, complementing the ordinate-integrated law, where the outer
contribution is exactly zero.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- **Semigroup collapse of the Cauchy kernels.**  The ordinate product of two Cauchy kernels of
widths `a` and `h` integrates to the single kernel of width `a + h` evaluated at the centre.
Averaging in the ordinate therefore only moves the abscissa to the right; it produces no
information the pointwise statement does not already carry. -/
theorem integral_cauchyKernel_mul {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (hah : a ≠ h) :
    (∫ y : ℝ, (a / (a ^ 2 + y ^ 2)) * (h / (h ^ 2 + y ^ 2))) = Real.pi / (a + h) := by
  have hd : h ^ 2 - a ^ 2 ≠ 0 := by
    intro hz
    have hfac : (h - a) * (h + a) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hah (by linarith)
    · linarith
  have hA : ∀ y : ℝ, (0 : ℝ) < a ^ 2 + y ^ 2 := fun y => by positivity
  have hH : ∀ y : ℝ, (0 : ℝ) < h ^ 2 + y ^ 2 := fun y => by positivity
  have hpt : ∀ y : ℝ, (a / (a ^ 2 + y ^ 2)) * (h / (h ^ 2 + y ^ 2)) =
      (h / (h ^ 2 - a ^ 2)) * (a / (a ^ 2 + y ^ 2)) -
        (a / (h ^ 2 - a ^ 2)) * (h / (h ^ 2 + y ^ 2)) := by
    intro y
    have h1 := (hA y).ne'
    have h2 := (hH y).ne'
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub ((integrable_cauchyKernel (ne_of_gt ha)).const_mul _)
      ((integrable_cauchyKernel (ne_of_gt hh)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_cauchyKernel_pos ha, integral_cauchyKernel_pos hh]
  have hsum : a + h ≠ 0 := by positivity
  field_simp
  ring

/-- **Averaging in the ordinate is moving right in the abscissa.**  A line-conjugate pair averaged
against a Cauchy weight of width `h` equals `π` times the same pair at abscissa shifted right by
`h`, evaluated at the centre.  Ordinate averaging therefore cannot separate an off-line zero from
its absence: it only re-evaluates the pointwise criterion further from the critical line, where the
criterion is weaker. -/
theorem integral_hadamardPair_cauchy_average {x δ h : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hxδ : δ ^ 2 < x ^ 2) (hne1 : x - δ ≠ h) (hne2 : x + δ ≠ h) :
    (∫ y : ℝ, ((x - δ) / ((x - δ) ^ 2 + y ^ 2) + (x + δ) / ((x + δ) ^ 2 + y ^ 2)) *
        (h / (h ^ 2 + y ^ 2))) =
      Real.pi * (1 / (x + h - δ) + 1 / (x + h + δ)) := by
  have h1 : 0 < x - δ := by nlinarith
  have h2 : 0 < x + δ := by nlinarith
  have hpt : ∀ y : ℝ, ((x - δ) / ((x - δ) ^ 2 + y ^ 2) + (x + δ) / ((x + δ) ^ 2 + y ^ 2)) *
      (h / (h ^ 2 + y ^ 2)) =
      ((x - δ) / ((x - δ) ^ 2 + y ^ 2)) * (h / (h ^ 2 + y ^ 2)) +
        ((x + δ) / ((x + δ) ^ 2 + y ^ 2)) * (h / (h ^ 2 + y ^ 2)) := by
    intro y; ring
  have hbound : ∀ a : ℝ, 0 < a → ∀ y : ℝ, ‖a / (a ^ 2 + y ^ 2)‖ ≤ 1 / a := by
    intro a hapos y
    have h1 : (0 : ℝ) < a ^ 2 + y ^ 2 := by positivity
    have key : 1 / a - a / (a ^ 2 + y ^ 2) = y ^ 2 / (a * (a ^ 2 + y ^ 2)) := by
      field_simp; ring
    have hnn : (0 : ℝ) ≤ y ^ 2 / (a * (a ^ 2 + y ^ 2)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hint1 : Integrable (fun y : ℝ =>
      ((x - δ) / ((x - δ) ^ 2 + y ^ 2)) * (h / (h ^ 2 + y ^ 2))) := by
    refine (integrable_cauchyKernel (ne_of_gt hh)).bdd_mul (c := 1 / (x - δ))
      (Measurable.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun y => hbound _ h1 y)
  have hint2 : Integrable (fun y : ℝ =>
      ((x + δ) / ((x + δ) ^ 2 + y ^ 2)) * (h / (h ^ 2 + y ^ 2))) := by
    refine (integrable_cauchyKernel (ne_of_gt hh)).bdd_mul (c := 1 / (x + δ))
      (Measurable.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun y => hbound _ h2 y)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint1 hint2,
    integral_cauchyKernel_mul h1 hh hne1, integral_cauchyKernel_mul h2 hh hne2]
  have e1 : x - δ + h = x + h - δ := by ring
  have e2 : x + δ + h = x + h + δ := by ring
  rw [e1, e2]
  ring

end

end RHTower
