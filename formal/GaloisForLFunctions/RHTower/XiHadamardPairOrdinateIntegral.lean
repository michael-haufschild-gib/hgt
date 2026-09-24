import GaloisForLFunctions.RHTower.XiLogDerivReLowHeight

/-!
# The ordinate-integrated pair law

Integrating a line-conjugate pair over the ordinate collapses the disk law to a counting statement.
Each half is a Cauchy kernel, so it integrates to `π` times the sign of its centred abscissa:

```text
∫_ℝ ( (x-δ)/((x-δ)²+y²) + (x+δ)/((x+δ)²+y²) ) dy  =  2π  if δ² < x² ,   0  if x² < δ² .
```

A zero strictly closer to the critical line than `s` contributes the full `2π`; a zero further out
contributes exactly `0`, its two halves cancelling.  The pointwise disk law of
`XiHadamardPairSignLaw` therefore has an exact integrated counting form.

The final theorem records the general shape of the unconditional region: any ordinate floor `H` for
off-line divisor copies yields the criterion on the box `Re s > 1/2`, `|Im s| ≤ H - 1/2`.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

theorem integrable_cauchyKernel {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun y : ℝ => a / (a ^ 2 + y ^ 2)) := by
  have hfun : (fun y : ℝ => a / (a ^ 2 + (a * y) ^ 2)) =
      fun y : ℝ => a⁻¹ * (1 + y ^ 2)⁻¹ := by
    funext y
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    field_simp
  refine (MeasureTheory.integrable_comp_mul_left_iff
    (fun y : ℝ => a / (a ^ 2 + y ^ 2)) ha).mp ?_
  rw [hfun]
  exact integrable_inv_one_add_sq.const_mul _

theorem integral_cauchyKernel_pos {a : ℝ} (ha : 0 < a) :
    (∫ y : ℝ, a / (a ^ 2 + y ^ 2)) = Real.pi := by
  have hne : a ≠ 0 := ne_of_gt ha
  have hfun : (fun y : ℝ => a / (a ^ 2 + (a * y) ^ 2)) =
      fun y : ℝ => a⁻¹ * (1 + y ^ 2)⁻¹ := by
    funext y
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 hne
    field_simp
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => a / (a ^ 2 + y ^ 2)) a
  rw [show (∫ y : ℝ, a / (a ^ 2 + (a * y) ^ 2)) = a⁻¹ * Real.pi by
    rw [hfun, integral_const_mul, integral_univ_inv_one_add_sq]] at h
  rw [smul_eq_mul, abs_of_pos (by positivity : (0:ℝ) < a⁻¹)] at h
  have hainv : a⁻¹ ≠ 0 := inv_ne_zero hne
  field_simp at h
  linarith [h]

theorem integral_cauchyKernel_neg {a : ℝ} (ha : a < 0) :
    (∫ y : ℝ, a / (a ^ 2 + y ^ 2)) = -Real.pi := by
  have h := integral_cauchyKernel_pos (a := -a) (by linarith)
  rw [← neg_eq_iff_eq_neg, ← integral_neg]
  refine h ▸ integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show -(a / (a ^ 2 + y ^ 2)) = (-a) / ((-a) ^ 2 + y ^ 2)
  rw [show ((-a) ^ 2 : ℝ) = a ^ 2 by ring]
  ring

/-- **Ordinate-integrated pair law, inner case.**  A zero strictly closer to the line than `s`
contributes `2π` to the ordinate integral of the pair. -/
theorem integral_hadamardPair_inner {x δ : ℝ} (hx : 0 < x) (h : δ ^ 2 < x ^ 2) :
    (∫ y : ℝ, ((x - δ) / ((x - δ) ^ 2 + y ^ 2) + (x + δ) / ((x + δ) ^ 2 + y ^ 2))) =
      2 * Real.pi := by
  have h1 : 0 < x - δ := by nlinarith
  have h2 : 0 < x + δ := by nlinarith
  rw [integral_add (integrable_cauchyKernel (ne_of_gt h1))
    (integrable_cauchyKernel (ne_of_gt h2)),
    integral_cauchyKernel_pos h1, integral_cauchyKernel_pos h2]
  ring

/-- **Ordinate-integrated pair law, outer case.**  A zero further from the line than `s`
contributes exactly `0`: the two halves cancel. -/
theorem integral_hadamardPair_outer {x δ : ℝ} (hx : 0 < x) (h : x ^ 2 < δ ^ 2) :
    (∫ y : ℝ, ((x - δ) / ((x - δ) ^ 2 + y ^ 2) + (x + δ) / ((x + δ) ^ 2 + y ^ 2))) = 0 := by
  rcases lt_or_gt_of_ne (show δ ≠ 0 by intro hz; rw [hz] at h; nlinarith) with hδ | hδ
  · have h1 : 0 < x - δ := by nlinarith
    have h2 : x + δ < 0 := by nlinarith
    rw [integral_add (integrable_cauchyKernel (ne_of_gt h1))
      (integrable_cauchyKernel (ne_of_lt h2)),
      integral_cauchyKernel_pos h1, integral_cauchyKernel_neg h2]
    ring
  · have h1 : x - δ < 0 := by nlinarith
    have h2 : 0 < x + δ := by nlinarith
    rw [integral_add (integrable_cauchyKernel (ne_of_lt h1))
      (integrable_cauchyKernel (ne_of_gt h2)),
      integral_cauchyKernel_neg h1, integral_cauchyKernel_pos h2]
    ring

/-- **Height floor to unconditional region.**  Any bound `H` on the ordinate of off-line divisor
copies yields the criterion on the whole box `Re s > 1/2`, `|Im s| ≤ H - 1/2`. -/
theorem re_logDeriv_xi_nonneg_of_offLine_height {H : ℝ}
    (hH : ∀ q : XiZeroCopy, ((q.1 : ℂ)).re ≠ 1 / 2 → H ≤ |((q.1 : ℂ)).im|)
    {s : ℂ} (hs : 1 / 2 < s.re) (ht : |s.im| ≤ H - 1 / 2) :
    0 ≤ (logDeriv xi s).re := by
  by_cases hxi : xi s = 0
  · rw [logDeriv_xi_eq_zero_of_xi_eq_zero hxi]; simp
  refine re_logDeriv_xi_nonneg_of_near_zeros hs hxi (fun q hy => ?_)
  by_cases hoff : ((q.1 : ℂ)).re = 1 / 2
  · rw [hoff]; nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)]
  · exfalso
    have hgamma := hH q hoff
    have h1 : |s.im - ((q.1 : ℂ)).im| < 1 / 2 := by
      nlinarith [sq_abs (s.im - ((q.1 : ℂ)).im), abs_nonneg (s.im - ((q.1 : ℂ)).im)]
    have hrw : ((q.1 : ℂ)).im = s.im - (s.im - ((q.1 : ℂ)).im) := by ring
    have h2 : |((q.1 : ℂ)).im| < H := by
      calc |((q.1 : ℂ)).im| = |s.im - (s.im - ((q.1 : ℂ)).im)| := by rw [← hrw]
        _ ≤ |s.im| + |s.im - ((q.1 : ℂ)).im| := abs_sub _ _
        _ < H := by linarith
    linarith

end

end RHTower
