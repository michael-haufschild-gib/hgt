import GaloisForLFunctions.RHTower.BurnolSoninEvaluationAperture
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.Inversion

/-!
# Gaussian smoothing and the archimedean Mellin--Fourier exchange

The completed Mellin evaluator factors through the Gaussian smoothing family

`G f u = ∫_ℝ f t exp (-π u t²) dt`,

because the Gamma integral resolves the power weight:

`π^(-w/2) Γ(w/2) t^(-w) = ∫_0^∞ u^(w/2-1) exp (-π u t²) du`.

Under the Fourier transform the smoothing family obeys the exact inversion law

`G (𝓕 f) u = u^(-1/2) G f (1/u)`,

which is the multiplication formula against the self-dual Gaussian.  Together these two facts are
the analytic content of the archimedean functional equation relating the completed Mellin transform
of `f` at `w` to that of `𝓕 f` at `1 - w`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace RHTower

/-- Gaussian smoothing of a function on the line at scale `u`. -/
def gaussianSmoothing (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, f t * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)

theorem integrable_gaussianKernel {u : ℝ} (hu : 0 < u) :
    Integrable fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
  have hb : 0 < ((Real.pi : ℂ) * (u : ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have := Real.pi_pos
    nlinarith
  have := integrable_cexp_neg_mul_sq hb
  refine this.congr ?_
  filter_upwards with t
  congr 1
  ring

theorem fourier_gaussianKernel {u : ℝ} (hu : 0 < u) :
    (𝓕 fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) =
      fun t : ℝ => 1 / (u : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (t : ℂ) ^ 2) := by
  have hb : 0 < ((u : ℂ)).re := by simpa using hu
  exact fourier_gaussian_pi hb

/-- **Multiplication formula against the Gaussian.**  Gaussian smoothing of the Fourier transform
is the reciprocal-scale smoothing of the function itself. -/
theorem gaussianSmoothing_fourier {f : ℝ → ℂ} (hf : Integrable f) {u : ℝ} (hu : 0 < u) :
    gaussianSmoothing (𝓕 f) u =
      1 / (u : ℂ) ^ (1 / 2 : ℂ) * gaussianSmoothing f u⁻¹ := by
  have hg : Integrable fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) :=
    integrable_gaussianKernel hu
  have hflip := (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg)
  have hkey : (∫ ξ : ℝ, (𝓕 f) ξ * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (ξ : ℂ) ^ 2)) =
      ∫ x : ℝ, f x *
        (𝓕 fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) x := by
    simpa [smul_eq_mul] using! hflip
  rw [gaussianSmoothing, hkey, fourier_gaussianKernel hu, gaussianSmoothing,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  have huinv : ((u⁻¹ : ℝ) : ℂ) = ((u : ℂ))⁻¹ := by push_cast; ring
  rw [huinv]
  have hne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
  have hexp : -(Real.pi : ℂ) / (u : ℂ) * (x : ℂ) ^ 2 =
      -(Real.pi : ℂ) * ((u : ℂ))⁻¹ * (x : ℂ) ^ 2 := by
    field_simp
  rw [hexp]
  ring


/-! ## The Gamma resolution of the power weight -/

theorem re_div_two (w : ℂ) : (w / 2).re = w.re / 2 := by
  simp

/-- **Gamma resolution of the completed power weight.**  The completed Mellin weight is the Gamma
integral of the Gaussian family. -/
theorem integral_Ioi_gaussianPower {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 < t) :
    (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
        Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) =
      mellinCompletionFactor w * (t : ℂ) ^ (-w) := by
  have hr : 0 < Real.pi * t ^ 2 := by positivity
  have ha : 0 < (w / 2).re := by
    rw [re_div_two]
    linarith
  have hcalc := integral_cpow_mul_exp_neg_mul_Ioi (a := w / 2) ha hr
  have hcongr : (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
      Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
        Complex.exp (-(((Real.pi * t ^ 2 : ℝ) : ℂ) * (u : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro u _
    have hexp : -(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2 =
        -(((Real.pi * t ^ 2 : ℝ) : ℂ) * (u : ℂ)) := by
      push_cast
      ring
    dsimp only
    rw [hexp]
  rw [hcongr, hcalc, mellinCompletionFactor]
  have hpine : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hbase : ((1 / (Real.pi * t ^ 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hlog : Real.log (1 / (Real.pi * t ^ 2)) =
      -(Real.log Real.pi) + -(2 * Real.log t) := by
    rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt Real.pi_pos) (by positivity),
      Real.log_pow]
    push_cast
    ring
  have hstep : ((1 / (Real.pi * t ^ 2 : ℝ) : ℝ) : ℂ) ^ (w / 2) =
      (Real.pi : ℂ) ^ (-w / 2) * ((t : ℝ) : ℂ) ^ (-w) := by
    rw [Complex.cpow_def_of_ne_zero hbase, Complex.cpow_def_of_ne_zero hpine,
      Complex.cpow_def_of_ne_zero htne, ← Complex.exp_add,
      ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log Real.pi_pos.le,
      ← Complex.ofReal_log ht.le, hlog]
    congr 1
    push_cast
    ring
  rw [show ((1 : ℂ) / ((Real.pi * t ^ 2 : ℝ) : ℂ)) =
      ((1 / (Real.pi * t ^ 2 : ℝ) : ℝ) : ℂ) from by push_cast; ring, hstep]
  ring


/-! ## Even carriers -/

theorem gaussianKernel_ofReal (u t : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) =
      ((Real.exp (-(Real.pi * u * t ^ 2)) : ℝ) : ℂ) := by
  rw [show (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)
      = ((-(Real.pi * u * t ^ 2) : ℝ) : ℂ) from by push_cast; ring,
    ← Complex.ofReal_exp]

theorem norm_gaussianKernel_le_one {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)‖ ≤ 1 := by
  rw [gaussianKernel_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_one_iff.mpr ?_
  have : 0 ≤ Real.pi * u * t ^ 2 := by positivity
  linarith

theorem integrable_mul_gaussianKernel {f : ℝ → ℂ} (hf : Integrable f) {u : ℝ} (hu : 0 ≤ u) :
    Integrable fun t : ℝ => f t * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
  refine hf.norm.mono' ?_ ?_
  · exact hf.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul]
    calc ‖f t‖ * ‖Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)‖
        ≤ ‖f t‖ * 1 := by
          exact mul_le_mul_of_nonneg_left (norm_gaussianKernel_le_one hu t) (norm_nonneg _)
      _ = ‖f t‖ := mul_one _

/-- On an even carrier the Gaussian smoothing is twice its half-line smoothing. -/
theorem gaussianSmoothing_of_even {f : ℝ → ℂ} (hf : Integrable f)
    (heven : ∀ t : ℝ, f (-t) = f t) {u : ℝ} (hu : 0 ≤ u) :
    gaussianSmoothing f u =
      2 * ∫ t in Ioi (0 : ℝ), f t * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
  set h : ℝ → ℂ :=
    fun t => f t * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) with hh
  have hheven : ∀ t : ℝ, h (-t) = h t := by
    intro t
    simp only [hh, heven t]
    congr 2
    push_cast
    ring
  have hint : Integrable h := integrable_mul_gaussianKernel hf hu
  have hsplit := integral_add_compl (measurableSet_Iio (a := (0 : ℝ))) hint
  rw [compl_Iio, integral_Ici_eq_integral_Ioi] at hsplit
  have hrefl : (∫ x in Iio (0 : ℝ), h x) = ∫ x in Ioi (0 : ℝ), h x := by
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Ioi (0 : ℝ)) = Iio 0 := by
      ext x
      simp
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
      measurableEmbedding_neg h (Ioi (0 : ℝ))
    rw [hpre] at hmp
    rw [← hmp]
    exact setIntegral_congr_fun measurableSet_Iio fun x _ => (hheven x).symm
  rw [hrefl] at hsplit
  rw [gaussianSmoothing, ← hsplit]
  ring

end RHTower
