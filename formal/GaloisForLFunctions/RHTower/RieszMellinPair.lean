import GaloisForLFunctions.RHTower.SmoothedInverseMellin

/-!
# The Mellin pair of the Riesz kernel

The kernel `1/w²` of the second-order Riesz mean is the Mellin transform of the truncated logarithm:

```text
∫_1^∞ (log x) x^{-w-1} dx = 1/w² ,        Re w > 0 .
```

The antiderivative is `-(log x) x^{-w}/w - x^{-w}/w²`; it vanishes at infinity because `Re w > 0`
and takes the value `-1/w²` at `x = 1`.  The integrand is dominated by `x^{-Re w/2 - 1}` there,
using `log x ≤ (2/a) x^{a/2}`, which is `log t ≤ t - 1` applied to `t = x^{a/2}`.

This is the transform identity that turns the vertical-line representation of a Riesz mean into a
Dirichlet series, and it is the companion of the kernel size estimate on the line.
-/

noncomputable section

open MeasureTheory Real Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The logarithm grows more slowly than any positive power. -/
theorem log_le_rpow_div {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (2 / a) * x ^ (a / 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hpow : (0 : ℝ) < x ^ (a / 2) := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log (x ^ (a / 2)) ≤ x ^ (a / 2) := by
    have h := Real.log_le_sub_one_of_pos hpow
    linarith
  rw [Real.log_rpow hx0] at hlog
  have ha2 : (0 : ℝ) < 2 / a := by positivity
  have ha' : a ≠ 0 := ne_of_gt ha
  have h2 := mul_le_mul_of_nonneg_left hlog ha2.le
  rw [show (2 / a) * (a / 2 * Real.log x) = Real.log x by field_simp] at h2
  exact h2

/-- The logarithm times a negative power tends to zero. -/
theorem tendsto_log_mul_rpow_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.log x * x ^ (-a)) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun x : ℝ => (2 / a) * x ^ (-(a / 2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < a / 2 by linarith)).const_mul (2 / a)
    simpa using h
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow : (0 : ℝ) < x ^ (-a) := Real.rpow_pos_of_pos hx0 _
  have hbound := log_le_rpow_div ha hx
  have hcomb : Real.log x * x ^ (-a) ≤ (2 / a) * (x ^ (a / 2) * x ^ (-a)) := by
    have := mul_le_mul_of_nonneg_right hbound hpow.le
    calc Real.log x * x ^ (-a) ≤ (2 / a) * x ^ (a / 2) * x ^ (-a) := this
      _ = (2 / a) * (x ^ (a / 2) * x ^ (-a)) := by ring
  have hmerge : x ^ (a / 2) * x ^ (-a) = x ^ (-(a / 2)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [hmerge] at hcomb
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hcomb

/-- The antiderivative of `(log x) x^{-w-1}`. -/
def rieszMellinAntideriv (w : ℂ) (y : ℝ) : ℂ :=
  -((Real.log y : ℂ) * (y : ℂ) ^ (-w)) / w - (y : ℂ) ^ (-w) / w ^ 2

theorem hasDerivAt_rieszMellinAntideriv {w : ℂ} (hw : w ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rieszMellinAntideriv w) ((Real.log x : ℂ) * (x : ℂ) ^ (-w - 1)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0
  have hwneg : -w ≠ 0 := neg_ne_zero.2 hw
  have hlog : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    (Real.hasDerivAt_log hx0).ofReal_comp
  have hcpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-w)) ((-w) * (x : ℂ) ^ (-w - 1)) x :=
    hasDerivAt_ofReal_cpow_const hx0 hwneg
  have hsplit : (x : ℂ) ^ (-w - 1) = (x : ℂ) ^ (-w) / (x : ℂ) := by
    rw [Complex.cpow_sub _ _ hxc, Complex.cpow_one]
  have hprod := hlog.mul hcpow
  have hterm1 := (hprod.neg).div_const w
  have hterm2 := hcpow.div_const (w ^ 2)
  have hres := hterm1.sub hterm2
  have hval : -(((x⁻¹ : ℝ) : ℂ) * (x : ℂ) ^ (-w)
        + (Real.log x : ℂ) * ((-w) * (x : ℂ) ^ (-w - 1))) / w
      - (-w) * (x : ℂ) ^ (-w - 1) / w ^ 2
      = (Real.log x : ℂ) * (x : ℂ) ^ (-w - 1) := by
    have hinv : ((x⁻¹ : ℝ) : ℂ) * (x : ℂ) ^ (-w) = (x : ℂ) ^ (-w - 1) := by
      rw [hsplit, Complex.ofReal_inv]
      field_simp
    rw [hinv]
    field_simp
    ring
  rw [← hval]
  exact hres

theorem tendsto_rieszMellinAntideriv {w : ℂ} (hw : 0 < w.re) :
    Tendsto (rieszMellinAntideriv w) atTop (𝓝 0) := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hnormw : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwne
  have h1 : Tendsto (fun y : ℝ => -((Real.log y : ℂ) * (y : ℂ) ^ (-w)) / w) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun y : ℝ => ‖w‖⁻¹ * (Real.log y * y ^ (-w.re))) atTop (𝓝 0) := by
      have h := (tendsto_log_mul_rpow_neg hw).const_mul (‖w‖⁻¹)
      simpa using h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hcpow : ‖(y : ℂ) ^ (-w)‖ = y ^ (-w).re := Complex.norm_cpow_eq_rpow_re_of_pos hy0 _
    have hre : (-w).re = -w.re := by simp
    rw [norm_div, norm_neg, norm_mul, hcpow, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hy)]
    exact le_of_eq (by ring)
  have h2 : Tendsto (fun y : ℝ => (y : ℂ) ^ (-w) / w ^ 2) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun y : ℝ => (‖w‖ ^ 2)⁻¹ * y ^ (-w.re)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop hw).const_mul ((‖w‖ ^ 2)⁻¹)
      simpa using h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hcpow : ‖(y : ℂ) ^ (-w)‖ = y ^ (-w).re := Complex.norm_cpow_eq_rpow_re_of_pos hy0 _
    have hre : (-w).re = -w.re := by simp
    rw [norm_div, hcpow, hre, norm_pow, div_eq_inv_mul]
  have hcomb := h1.sub h2
  rw [sub_zero] at hcomb
  exact hcomb

theorem integrableOn_log_cpow_neg_succ {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-w - 1)) (Set.Ioi (1 : ℝ)) := by
  have hmaj : IntegrableOn (fun x : ℝ => (2 / w.re) * x ^ (-(w.re / 2) - 1))
      (Set.Ioi (1 : ℝ)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -(w.re / 2) - 1) ?_ one_pos).const_mul _
    linarith
  refine Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans one_pos hx)
    have hwne : -w - 1 ≠ 0 := by
      intro h
      have : (-w - 1).re = 0 := by rw [h]; simp
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re] at this
      linarith
    have hc1 : ContinuousAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) x :=
      (Real.continuousAt_log hx0).ofReal.comp continuousAt_id
    have hc2 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-w - 1)) x :=
      (hasDerivAt_ofReal_cpow_const hx0 hwne).continuousAt
    exact (hc1.mul hc2).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
    have hcpow : ‖(x : ℂ) ^ (-w - 1)‖ = x ^ (-w - 1).re :=
      Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
    have hre : (-w - 1).re = -w.re - 1 := by simp
    rw [norm_mul, hcpow, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx1)]
    have hbound := log_le_rpow_div hw hx1
    have hpow : (0 : ℝ) < x ^ (-w.re - 1) := Real.rpow_pos_of_pos hx0 _
    have hstep : Real.log x * x ^ (-w.re - 1)
        ≤ (2 / w.re) * x ^ (w.re / 2) * x ^ (-w.re - 1) :=
      mul_le_mul_of_nonneg_right hbound hpow.le
    refine le_trans hstep (le_of_eq ?_)
    rw [mul_assoc, ← Real.rpow_add hx0]
    congr 2
    ring

/-- **The Mellin pair of the Riesz kernel.** -/
theorem integral_Ioi_log_cpow_neg_succ {w : ℂ} (hw : 0 < w.re) :
    ∫ x in Set.Ioi (1 : ℝ), (Real.log x : ℂ) * (x : ℂ) ^ (-w - 1) = 1 / w ^ 2 := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hcont : ContinuousWithinAt (rieszMellinAntideriv w) (Set.Ici (1 : ℝ)) 1 :=
    (hasDerivAt_rieszMellinAntideriv hwne one_pos).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (rieszMellinAntideriv w) ((Real.log x : ℂ) * (x : ℂ) ^ (-w - 1)) x := by
    intro x hx
    exact hasDerivAt_rieszMellinAntideriv hwne (lt_trans one_pos hx)
  have hone : rieszMellinAntideriv w 1 = -(1 / w ^ 2) := by
    simp [rieszMellinAntideriv]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (integrableOn_log_cpow_neg_succ hw)
    (tendsto_rieszMellinAntideriv hw), hone]
  ring

end GaloisForLFunctions.RHTower

end
