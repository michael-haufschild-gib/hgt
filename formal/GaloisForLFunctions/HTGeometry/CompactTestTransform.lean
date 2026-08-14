import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The entire Fourier extension of a compactly supported test function

For a smooth function `ψ` supported in `[-M, M]` the integral

`Ψ(z) = ∫ ψ(L) e^{izL} dL`

is entire, and two integrations by parts give `z² Ψ(z) = -∫ ψ''(L) e^{izL} dL`, so on every
horizontal strip `Ψ` decays like `|z|^{-2}`.  This is the multiplier that makes a contour shift
legitimate for a boundary datum that is only square integrable.
-/

open Complex MeasureTheory Set Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The complex Fourier extension of a test function. -/
def testTransform (ψ : ℝ → ℂ) (z : ℂ) : ℂ := ∫ L : ℝ, ψ L * Complex.exp (Complex.I * z * (L : ℂ))

theorem norm_exp_I_mul (z : ℂ) (L : ℝ) :
    ‖Complex.exp (Complex.I * z * (L : ℂ))‖ = Real.exp (-(L * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp
  ring

/-- The integrand of the test transform is integrable for a compactly supported continuous
function. -/
theorem integrable_testTransform_integrand {ψ : ℝ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (z : ℂ) :
    Integrable (fun L : ℝ => ψ L * Complex.exp (Complex.I * z * (L : ℂ))) := by
  refine (Continuous.integrable_of_hasCompactSupport ?_ ?_)
  · exact hc.mul (Complex.continuous_exp.comp (by fun_prop))
  · exact hs.mul_right

/-- The test transform is entire. -/
theorem differentiable_testTransform {ψ : ℝ → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    Differentiable ℂ (testTransform ψ) := by
  intro z₀
  set bound : ℝ → ℝ := fun L =>
    ‖ψ L‖ * (|L| * Real.exp ((|z₀.im| + 1) * |L|)) with hbound
  have hboundc : Continuous bound := by
    refine hc.norm.mul (continuous_abs.mul ?_)
    exact Real.continuous_exp.comp (continuous_const.mul continuous_abs)
  have hboundcs : HasCompactSupport bound := by
    refine HasCompactSupport.mul_right ?_
    exact hs.norm
  have hboundint : Integrable bound := hboundc.integrable_of_hasCompactSupport hboundcs
  have hmeas : ∀ᶠ w in nhds z₀,
      AEStronglyMeasurable (fun L : ℝ => ψ L * Complex.exp (Complex.I * w * (L : ℂ)))
        MeasureTheory.volume := by
    filter_upwards with w
    exact (integrable_testTransform_integrand hc hs w).aestronglyMeasurable
  have hint : Integrable (fun L : ℝ => ψ L * Complex.exp (Complex.I * z₀ * (L : ℂ))) :=
    integrable_testTransform_integrand hc hs z₀
  have hderivmeas : AEStronglyMeasurable
      (fun L : ℝ => ψ L * (Complex.I * (L : ℂ)) * Complex.exp (Complex.I * z₀ * (L : ℂ)))
      MeasureTheory.volume := by
    refine Continuous.aestronglyMeasurable ?_
    exact (hc.mul (by fun_prop)).mul (Complex.continuous_exp.comp (by fun_prop))
  have hdiff : ∀ᵐ L : ℝ, ∀ w ∈ Metric.ball z₀ 1,
      HasDerivAt (fun w : ℂ => ψ L * Complex.exp (Complex.I * w * (L : ℂ)))
        (ψ L * (Complex.I * (L : ℂ)) * Complex.exp (Complex.I * w * (L : ℂ))) w := by
    filter_upwards with L w _
    have hlin : HasDerivAt (fun w : ℂ => Complex.I * w * (L : ℂ)) (Complex.I * (L : ℂ)) w := by
      have h1 : HasDerivAt (fun w : ℂ => Complex.I * w) Complex.I w := by
        simpa using (hasDerivAt_id w).const_mul Complex.I
      simpa [mul_comm] using h1.mul_const ((L : ℂ))
    have hexp := hlin.cexp
    have := hexp.const_mul (ψ L)
    convert this using 1
    ring
  have hbnd : ∀ᵐ L : ℝ, ∀ w ∈ Metric.ball z₀ 1,
      ‖ψ L * (Complex.I * (L : ℂ)) * Complex.exp (Complex.I * w * (L : ℂ))‖ ≤ bound L := by
    filter_upwards with L w hw
    have hwim : |w.im - z₀.im| < 1 := by
      have := Complex.abs_im_sub_le_norm w z₀ -- placeholder
      have hdist : dist w z₀ < 1 := Metric.mem_ball.mp hw
      have himle : |w.im - z₀.im| ≤ dist w z₀ := by
        simpa [Complex.dist_eq, Complex.sub_im] using Complex.abs_im_le_norm (w - z₀)
      exact lt_of_le_of_lt himle hdist
    have hwbound : |w.im| ≤ |z₀.im| + 1 := by
      have := abs_sub_abs_le_abs_sub w.im z₀.im
      linarith [hwim, this]
    rw [norm_mul, norm_mul, norm_exp_I_mul, Complex.norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, hbound]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg L)
    refine Real.exp_le_exp.mpr ?_
    calc -(L * w.im) ≤ |L * w.im| := neg_le_abs _
      _ = |L| * |w.im| := abs_mul L w.im
      _ ≤ |L| * (|z₀.im| + 1) := mul_le_mul_of_nonneg_left hwbound (abs_nonneg L)
      _ = (|z₀.im| + 1) * |L| := by ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun w L =>
      ψ L * Complex.exp (Complex.I * w * (L : ℂ)))
    (F' := fun w L => ψ L * (Complex.I * (L : ℂ)) * Complex.exp (Complex.I * w * (L : ℂ)))
    (bound := bound) (ε := 1) (by norm_num) hmeas hint hderivmeas hbnd hboundint hdiff
  exact (hres.2).differentiableAt

end

end GaloisForLFunctions.HTGeometry
