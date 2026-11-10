import GaloisForLFunctions.ExceptionalLayerTheory.GaussianCentredVaughanCurrent
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Analytic dependence of Gaussian arithmetic errors on damping

Positive real damping gives local normal convergence of the arithmetic
series. The logarithmic continuum term has the same holomorphic domain.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction
open MeasureTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem differentiableAt_gaussianDampingSeries
    (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ k) {ε : ℂ} (hε : 0 < ε.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, a n * Complex.exp (-(z * (n : ℂ) ^ 2))) ε := by
  let U : Set ℂ := {z | ε.re / 2 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hεU : ε ∈ U := by dsimp only [U, mem_setOf_eq]; linarith only [hε]
  have hs := (RHTower.summable_pow_mul_exp_neg_nat_sq k (by positivity : 0 < ε.re / 2)).mul_left C
  have hf (n : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => a n * Complex.exp (-(z * (n : ℂ) ^ 2))) U := by fun_prop
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ U) :
      ‖a n * Complex.exp (-(z * (n : ℂ) ^ 2))‖ ≤
        C * ((n : ℝ) ^ k * Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2)) := by
    have hr : (-(z * (n : ℂ) ^ 2)).re = -z.re * (n : ℝ) ^ 2 := by
      simp only [Complex.neg_re, Complex.mul_re, pow_two, Complex.mul_im,
        Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero, add_zero]
      ring
    rw [norm_mul, Complex.norm_exp, hr]
    have he : Real.exp (-z.re * (n : ℝ) ^ 2) ≤ Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (le_of_lt hz) (sq_nonneg (n : ℝ))
      linarith only [hh]
    calc
      _ ≤ (C * (n : ℝ) ^ k) * Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2) :=
        mul_le_mul (ha n) he (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  exact (Complex.differentiableOn_tsum_of_summable_norm hs hf hU hb).differentiableAt (hU.mem_nhds hεU)


private theorem norm_logMellinWeight_positive {w ε : ℂ} {b x : ℝ} (hx : 0 < x) :
    ‖gaussianLogMellinWeight w ε b x‖ =
      |Real.log (x / b)| * (x ^ w.re * Real.exp (-ε.re * x ^ 2)) := by
  rw [gaussianLogMellinWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    gaussianMellinWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  congr 3
  simp [pow_two]

private theorem gaussianLogMellinWeight_add_two (w ε : ℂ) (b : ℝ) {x : ℝ} (hx : 0 < x) :
    gaussianLogMellinWeight (w + 2) ε b x =
      (x : ℂ) ^ 2 * gaussianLogMellinWeight w ε b x := by
  rw [gaussianLogMellinWeight, gaussianLogMellinWeight, gaussianMellinWeight,
    gaussianMellinWeight, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_ofNat]
  ring

/-- The logarithmic continuum is holomorphic throughout positive real damping. -/
theorem hasDerivAt_integral_gaussianLogMellinWeight {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun z => ∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w z b x)
      (∫ x in Ioi (0 : ℝ), -gaussianLogMellinWeight (w + 2) ε b x) ε := by
  let δ := ε.re / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hw2 : 0 < (w + 2).re := by
    simp only [Complex.add_re, show (2 : ℂ).re = 2 by norm_num]
    linarith only [hw]
  have hball (z : ℂ) (hz : z ∈ ball ε δ) : δ < z.re := by
    have hr := Complex.abs_re_le_norm (z - ε)
    have hn : ‖z - ε‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    rw [Complex.sub_re] at hr
    have hh := (abs_lt.mp (hr.trans_lt hn)).1
    dsimp only [δ] at hh ⊢
    linarith only [hh]
  have hint : IntegrableOn (fun x : ℝ => ‖gaussianLogMellinWeight (w + 2) (δ : ℂ) b x‖)
      (Ioi 0) := (integrableOn_gaussianLogMellinWeight hw2 (by simpa using hδ) hb).norm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (μ := volume.restrict (Ioi 0))
    (F := fun z x => gaussianLogMellinWeight w z b x)
    (F' := fun z x => -gaussianLogMellinWeight (w + 2) z b x)
    (bound := fun x => ‖gaussianLogMellinWeight (w + 2) (δ : ℂ) b x‖)
    (Metric.ball_mem_nhds ε hδ) ?_ ?_ ?_ ?_ hint ?_).2
  · filter_upwards [Metric.ball_mem_nhds ε hδ] with z hz
    exact (integrableOn_gaussianLogMellinWeight hw (hδ.trans (hball z hz)) hb).aestronglyMeasurable
  · exact integrableOn_gaussianLogMellinWeight hw hε hb
  · exact (integrableOn_gaussianLogMellinWeight hw2 hε hb).neg.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
    rw [norm_neg, norm_logMellinWeight_positive hx, norm_logMellinWeight_positive hx]
    simp only [Complex.ofReal_re]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (hball z hz).le) (sq_nonneg x)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
    have hd := (((hasDerivAt_id z).mul_const ((x : ℂ) ^ 2)).neg.cexp.const_mul
      ((x : ℂ) ^ w)).const_mul ((Real.log (x / b) : ℝ) : ℂ)
    apply hd.congr_deriv
    rw [gaussianLogMellinWeight_add_two w z b hx]
    dsimp only [gaussianLogMellinWeight, gaussianMellinWeight]
    simp only [Pi.neg_apply, one_mul, id_eq, neg_mul]
    ring

/-- Multiplication by the normalized damping preserves holomorphy of the
logarithmic continuum moment. -/
theorem differentiableAt_gaussianFirstMomentLogPole {s ε : ℂ}
    (hs : s.re < 2) (hε : 0 < ε.re) (t : ℝ) :
    DifferentiableAt ℂ (fun z => gaussianFirstMomentLogPole s z t) ε := by
  have hw : 0 < (2 - s).re := by
    simp only [Complex.sub_re, show (2 : ℂ).re = 2 by norm_num]
    linarith only [hs]
  exact (differentiableAt_id.div_const (t : ℂ)).mul
    (hasDerivAt_integral_gaussianLogMellinWeight hw hε (by norm_num : (0 : ℝ) < 1)).differentiableAt

end GaloisForLFunctions.ExceptionalLayerTheory
