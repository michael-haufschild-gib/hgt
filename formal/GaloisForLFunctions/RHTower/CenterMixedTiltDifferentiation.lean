import GaloisForLFunctions.RHTower.ThetaCuspTiltedSchwartz
import Mathlib
import GaloisForLFunctions.RHTower.RadialInteractionBound

/-!
# Differentiation of the tilted theta transform in the tilt parameter

The center-mixed Fourier computation needs the first moment of the exponentially tilted kernel to be
the derivative of the transform in the tilt:

`∂_a ∫ exp (a x) Φ x e^{-i s x / 2} dx = ∫ x exp (a x) Φ x e^{-i s x / 2} dx`.

This is differentiation under the integral sign.  The dominating function is supplied by the fact
that the tilted source `x ↦ exp (c x) Φ x` is a Schwartz function for every `|c| < 1`, so all of its
moments are integrable; bounding `exp (b x)` by `exp (c x) + exp (-c x)` on a ball of tilts covers
the whole ball at once.

The constraint `|c| < 1` is exactly the Fourier--Laplace strip of the theta kernel, and it is the
reason the center-mixed parameter is restricted to `0 < a < 1/2`: the weight `sinh (2 a w)` tilts by
`±2a`.
-/

open MeasureTheory Complex

namespace RHTower

/-- **Differentiation under the integral in the tilt parameter.** -/
theorem hasDerivAt_integral_exp_tilt (F : ℝ → ℂ) {a : ℝ} {S : Set ℝ} (hS : S ∈ nhds a)
    {bound : ℝ → ℝ}
    (hmeas : ∀ b : ℝ, AEStronglyMeasurable (fun x : ℝ => Complex.exp (b * x) * F x) volume)
    (hint : Integrable (fun x : ℝ => Complex.exp (a * x) * F x))
    (hmeas' : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) * Complex.exp (a * x) * F x) volume)
    (hbound : ∀ᵐ x : ℝ, ∀ b ∈ S, ‖(x : ℂ) * Complex.exp (b * x) * F x‖ ≤ bound x)
    (hbint : Integrable bound) :
    HasDerivAt (fun b : ℝ => ∫ x : ℝ, Complex.exp (b * x) * F x)
      (∫ x : ℝ, (x : ℂ) * Complex.exp (a * x) * F x) a := by
  have hderiv : ∀ᵐ x : ℝ, ∀ b ∈ S,
      HasDerivAt (fun c : ℝ => Complex.exp (c * x) * F x)
        ((x : ℂ) * Complex.exp (b * x) * F x) b := by
    filter_upwards with x
    intro b _
    have h1 : HasDerivAt (fun c : ℝ => ((c : ℂ) * (x : ℂ))) ((x : ℂ)) b := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := b)).mul_const ((x : ℂ))
    have h2 : HasDerivAt (fun c : ℝ => Complex.exp ((c : ℂ) * (x : ℂ)))
        (Complex.exp ((b : ℂ) * (x : ℂ)) * (x : ℂ)) b := by
      simpa using (Complex.hasDerivAt_exp ((b : ℂ) * (x : ℂ))).comp b h1
    have h3 := h2.mul_const (F x)
    convert h3 using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Filter.Eventually.of_forall hmeas) hint hmeas' hbound hbint hderiv).2

/-- The first moment of a tilted theta source is integrable inside the strip. -/
theorem integrable_abs_mul_thetaCuspTiltedSource {c : ℝ} (hc : |c| < 1) :
    Integrable fun x : ℝ => |x| * |thetaCuspTiltedSource c x| := by
  have h := (thetaCuspTiltedSchwartzReal c hc).integrable_pow_mul (volume : Measure ℝ) 1
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs]

/-- **The tilted theta transform is differentiable in the tilt, with the first moment as
derivative.** -/
theorem hasDerivAt_thetaCuspTiltTransform (s : ℝ) {a : ℝ} (ha : |a| < 1) :
    HasDerivAt
      (fun b : ℝ => ∫ x : ℝ, Complex.exp (b * x) *
        ((thetaCuspFullSource x : ℂ) * Complex.exp (-Complex.I * (s / 2 : ℝ) * x)))
      (∫ x : ℝ, (x : ℂ) * Complex.exp (a * x) *
        ((thetaCuspFullSource x : ℂ) * Complex.exp (-Complex.I * (s / 2 : ℝ) * x))) a := by
  classical
  set F : ℝ → ℂ := fun x =>
    (thetaCuspFullSource x : ℂ) * Complex.exp (-Complex.I * (s / 2 : ℝ) * x) with hF
  set c : ℝ := (|a| + 1) / 2 with hc
  have hcpos : |a| < c := by rw [hc]; linarith
  have hclt : |c| < 1 := by
    rw [hc, abs_of_nonneg (by positivity)]
    linarith
  have hcnegabs : |(-c)| < 1 := by rwa [abs_neg]
  set ε : ℝ := c - |a| with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hSmem : Metric.ball a ε ∈ nhds a := Metric.ball_mem_nhds a hεpos
  -- measurability
  have hΦmeas : Continuous fun x : ℝ => (thetaCuspFullSource x : ℂ) :=
    Complex.continuous_ofReal.comp contDiff_thetaCuspFullSource.continuous
  have hFcont : Continuous F := by
    rw [hF]
    exact hΦmeas.mul ((Complex.continuous_exp).comp (by fun_prop))
  have hmeas : ∀ b : ℝ, AEStronglyMeasurable (fun x : ℝ => Complex.exp (b * x) * F x) volume :=
    fun b => (((Complex.continuous_exp).comp (by fun_prop)).mul hFcont).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) * Complex.exp (a * x) * F x) volume :=
    ((Complex.continuous_ofReal.mul
      ((Complex.continuous_exp).comp (by fun_prop))).mul hFcont).aestronglyMeasurable
  -- the pointwise norm of the integrand
  have hnorm : ∀ (b x : ℝ), ‖Complex.exp ((b : ℂ) * (x : ℂ)) * F x‖
      = Real.exp (b * x) * |thetaCuspFullSource x| := by
    intro b x
    have hre : (-Complex.I * ((s / 2 : ℝ) : ℂ) * (x : ℂ)).re = 0 := by simp [Complex.mul_re]
    have hbx : ((b : ℂ) * (x : ℂ)).re = b * x := by simp [Complex.mul_re]
    rw [hF]
    simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, hre, hbx,
      Real.exp_zero, mul_one]
  -- integrability at the base point
  have hint : Integrable (fun x : ℝ => Complex.exp (a * x) * F x) := by
    have hbase : Integrable (fun x : ℝ => Real.exp (a * x) * thetaCuspFullSource x) := by
      simpa only [thetaCuspTiltedSchwartzReal_apply, thetaCuspTiltedSource] using
        (thetaCuspTiltedSchwartzReal a ha).integrable (μ := (volume : Measure ℝ))
    refine hbase.mono (hmeas a) ?_
    filter_upwards with x
    rw [hnorm a x, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  -- the dominating function
  set bound : ℝ → ℝ := fun x =>
    |x| * |thetaCuspTiltedSource c x| + |x| * |thetaCuspTiltedSource (-c) x| with hbd
  have hbint : Integrable bound := by
    rw [hbd]
    exact (integrable_abs_mul_thetaCuspTiltedSource hclt).add
      (integrable_abs_mul_thetaCuspTiltedSource hcnegabs)
  have hbound : ∀ᵐ x : ℝ, ∀ b ∈ Metric.ball a ε,
      ‖(x : ℂ) * Complex.exp (b * x) * F x‖ ≤ bound x := by
    filter_upwards with x
    intro b hb
    have hb' : |b - a| < ε := by
      simpa [Real.dist_eq] using hb
    have hbc : |b| < c := by
      have htri := abs_sub_abs_le_abs_sub b a
      have hlt : |b| < ε + |a| := by linarith
      rw [hε] at hlt
      linarith
    have hexp : Real.exp (b * x) ≤ Real.exp (c * x) + Real.exp (-c * x) := by
      rcases le_total 0 x with hx | hx
      · have : b * x ≤ c * x := by nlinarith [abs_le.mp hbc.le, le_abs_self b]
        have h1 := Real.exp_le_exp.mpr this
        linarith [Real.exp_pos (-c * x)]
      · have : b * x ≤ -c * x := by nlinarith [abs_le.mp hbc.le, neg_abs_le b]
        have h1 := Real.exp_le_exp.mpr this
        linarith [Real.exp_pos (c * x)]
    have hrw : ‖(x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ)) * F x‖
        = |x| * (Real.exp (b * x) * |thetaCuspFullSource x|) := by
      rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnorm b x]
    rw [hrw, hbd]
    have hΦ : (0:ℝ) ≤ |thetaCuspFullSource x| := abs_nonneg _
    have hxx : (0:ℝ) ≤ |x| := abs_nonneg _
    have hsplit : |x| * (Real.exp (b * x) * |thetaCuspFullSource x|)
        ≤ |x| * ((Real.exp (c * x) + Real.exp (-c * x)) * |thetaCuspFullSource x|) := by
      apply mul_le_mul_of_nonneg_left _ hxx
      exact mul_le_mul_of_nonneg_right hexp hΦ
    refine hsplit.trans (le_of_eq ?_)
    simp only [thetaCuspTiltedSource, abs_mul, abs_of_pos (Real.exp_pos _)]
    ring
  exact hasDerivAt_integral_exp_tilt F hSmem hmeas hint hmeas' hbound hbint

end RHTower
