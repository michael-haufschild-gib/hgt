import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.GaussianConeKernel
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian-damped coupling is an arithmetic heat average

The damped spline kernel is the Gaussian average of the compact-test arithmetic
Weil functional. A strip-uniform integrable majorant justifies exchanging the zero
sum with the Gaussian integral. Mixed differences give the same identity for the
natural-cone coupling, retaining the prime, archimedean and pole terms.
-/

noncomputable section

open Complex MeasureTheory Filter Set Zeta23

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

open ConeCoupling ArithmeticCastelnuovoSeveri HeckeKreinToeplitz
open ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open BiScaleUncertainty.ChebyshevGauge

/-- The actual arithmetic Weil functional along the cubic-spline translation orbit. -/
def arithmeticSplineProfile (t : ℝ) : ℂ :=
  RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (EF.weilTest (cx cubicSpline) (shiftTest (-t) (cx cubicSpline)))

theorem arithmeticSplineProfile_eq_tsum (t : ℝ) :
    arithmeticSplineProfile t = ∑' ρ : zetaZeroConfig.carrier, mult t ρ * wt ρ := by
  have hf := cx_contDiff contDiff_cubicSpline
  have hfc := cx_hasCompactSupport hasCompactSupport_cubicSpline
  have hg : ContDiff ℝ 2 (shiftTest (-t) (cx cubicSpline)) :=
    hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport (shiftTest (-t) (cx cubicSpline)) :=
    hfc.comp_homeomorph (Homeomorph.subRight (-t))
  unfold arithmeticSplineProfile
  rw [← RHTower.zeta_W_eq_weilFullFunctional_mixed hf hfc hg hgc]
  have hz : shiftTest 0 (cx cubicSpline) = cx cubicSpline := by
    funext u
    simp only [ArithmeticCastelnuovoSeveri.translate, sub_zero]
  have h := W_shiftTest_shiftTest zetaZeroConfig cubicSpline 0 (-t)
  rw [hz] at h
  simpa only [Complex.ofReal_zero, Complex.ofReal_neg, zero_sub, neg_neg] using h

private theorem integrable_heatExponential {b : ℝ} (hb : 0 < b) (z : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + z * y)) := by
  simpa only [add_zero] using
    integrable_cexp_quadratic (b := (b : ℂ)) (by exact hb) z 0

private theorem integral_heatExponential {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (∫ y : ℝ, Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + z * y)) =
      (Real.sqrt (Real.pi / b) : ℂ) * Complex.exp (z ^ 2 / (4 * b)) := by
  have hbase : ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / b) : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hb.le) (1 / 2 : ℝ)).symm
  simpa only [add_zero, neg_neg, zero_sub, mul_neg, div_neg, hbase] using
    integral_cexp_quadratic (b := -(b : ℂ)) (by simpa only [Complex.neg_re,
      Complex.ofReal_re] using (neg_lt_zero.mpr hb)) z 0

private def heatEnvelope (b y : ℝ) : ℝ :=
  ‖Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + (1 / 2 : ℂ) * y)‖ +
    ‖Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + (-1 / 2 : ℂ) * y)‖

private theorem integrable_heatEnvelope {b : ℝ} (hb : 0 < b) :
    Integrable (heatEnvelope b) :=
  (integrable_heatExponential hb (1 / 2)).norm.add
    (integrable_heatExponential hb (-1 / 2)).norm

private theorem heatExponential_le_envelope (b y : ℝ) {z : ℂ}
    (hz : |z.re| ≤ 1 / 2) :
    ‖Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + z * y)‖ ≤ heatEnvelope b y := by
  have hr (c : ℂ) :
      ‖Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + c * y)‖ =
        Real.exp (-b * y ^ 2 + c.re * y) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [← Complex.ofReal_pow, Complex.add_re, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  unfold heatEnvelope
  simp only [hr]
  rcases le_total 0 y with hy | hy
  · have hle : Real.exp (-b * y ^ 2 + z.re * y) ≤
        Real.exp (-b * y ^ 2 + (1 / 2 : ℂ).re * y) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right (abs_le.mp hz).2 hy
      norm_num only [Complex.div_ofNat_re, Complex.one_re]
      linarith only [h]
    linarith only [hle, (Real.exp_pos (-b * y ^ 2 + (-1 / 2 : ℂ).re * y)).le]
  · have hle : Real.exp (-b * y ^ 2 + z.re * y) ≤
        Real.exp (-b * y ^ 2 + (-1 / 2 : ℂ).re * y) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonpos_right (abs_le.mp hz).1 hy
      norm_num only [Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
      linarith only [h]
    linarith only [hle, (Real.exp_pos (-b * y ^ 2 + (1 / 2 : ℂ).re * y)).le]

private theorem norm_mult_le_abs (t : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖mult t ρ‖ ≤ Real.exp (|t| / 2) := by
  rw [norm_mult]
  have hs := zetaZeroConfig.strip ρ.val ρ.property
  have hz : |(ρ : ℂ).re - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  apply Real.exp_le_exp.mpr
  calc t * ((ρ : ℂ).re - 1 / 2) ≤ |t * ((ρ : ℂ).re - 1 / 2)| := le_abs_self _
    _ = |t| * |(ρ : ℂ).re - 1 / 2| := abs_mul _ _
    _ ≤ |t| * (1 / 2) := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ = |t| / 2 := by ring

private def heatTerm (b t : ℝ) (ρ : zetaZeroConfig.carrier) (y : ℝ) : ℂ :=
  Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + zeroOffset ρ * y) * (mult t ρ * wt ρ)

private theorem integrable_heatTerm {b : ℝ} (hb : 0 < b) (t : ℝ)
    (ρ : zetaZeroConfig.carrier) : Integrable (heatTerm b t ρ) :=
  (integrable_heatExponential hb (zeroOffset ρ)).mul_const _

private theorem summable_integral_norm_heatTerm {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Summable (fun ρ : zetaZeroConfig.carrier => ∫ y, ‖heatTerm b t ρ y‖) := by
  have hi := integrable_heatEnvelope hb
  have hn : ∀ y, 0 ≤ heatEnvelope b y := fun y => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbound (ρ : zetaZeroConfig.carrier) (y : ℝ) :
      ‖heatTerm b t ρ y‖ ≤ (Real.exp (|t| / 2) * ‖wt ρ‖) * heatEnvelope b y := by
    have hs := zetaZeroConfig.strip ρ.val ρ.property
    have hz : |(zeroOffset ρ).re| ≤ 1 / 2 := by
      rw [zeroOffset_re]
      exact abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    rw [heatTerm, norm_mul, norm_mul]
    have h := mul_le_mul (heatExponential_le_envelope b y hz)
      (mul_le_mul_of_nonneg_right (norm_mult_le_abs t ρ) (norm_nonneg (wt ρ)))
      (mul_nonneg (norm_nonneg (mult t ρ)) (norm_nonneg (wt ρ))) (hn y)
    exact h.trans_eq (mul_comm _ _)
  refine (summable_norm_wt.mul_left (Real.exp (|t| / 2) * ∫ y, heatEnvelope b y)).of_nonneg_of_le
    (fun ρ => integral_nonneg fun y => norm_nonneg _) fun ρ => ?_
  calc (∫ y, ‖heatTerm b t ρ y‖) ≤
        ∫ y, (Real.exp (|t| / 2) * ‖wt ρ‖) * heatEnvelope b y :=
      integral_mono (integrable_heatTerm hb t ρ).norm (hi.const_mul _) (hbound ρ)
    _ = (Real.exp (|t| / 2) * ∫ y, heatEnvelope b y) * ‖wt ρ‖ := by
      rw [integral_const_mul]
      ring

private theorem tsum_heatTerm (b t y : ℝ) :
    (∑' ρ : zetaZeroConfig.carrier, heatTerm b t ρ y) =
      (Real.exp (-b * y ^ 2) : ℂ) * arithmeticSplineProfile (t + y) := by
  rw [arithmeticSplineProfile_eq_tsum, ← tsum_mul_left, Complex.ofReal_exp]
  apply tsum_congr
  intro ρ
  simp only [heatTerm, mult, zeroOffset, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- Gaussian averaging of the arithmetic profile is absolutely integrable. -/
theorem integrable_gaussian_arithmeticSplineProfile {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Integrable (fun y : ℝ => (Real.exp (-b * y ^ 2) : ℂ) * arithmeticSplineProfile (t + y)) := by
  letI : Countable zetaZeroConfig.carrier :=
    (SquareRootThreshold.carrier_countable zetaZeroConfig).to_subtype
  have h := HTGeometry.integrable_tsum_of_summable_integral_norm
    (integrable_heatTerm hb t) (summable_integral_norm_heatTerm hb t)
  simpa only [tsum_heatTerm] using h

/-- The Gaussian integral of the arithmetic profile is the damped spectral kernel. -/
theorem integral_gaussian_arithmeticSplineProfile {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (∫ y : ℝ, (Real.exp (-b * y ^ 2) : ℂ) * arithmeticSplineProfile (t + y)) =
      (Real.sqrt (Real.pi / b) : ℂ) * gaussianConeKernel (1 / (4 * b)) t := by
  letI : Countable zetaZeroConfig.carrier :=
    (SquareRootThreshold.carrier_countable zetaZeroConfig).to_subtype
  rw [← funext (tsum_heatTerm b t)]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
    (integrable_heatTerm hb t) (summable_integral_norm_heatTerm hb t)]
  rw [gaussianConeKernel, ← tsum_mul_left]
  apply tsum_congr
  intro ρ
  simp only [heatTerm]
  rw [integral_mul_const, integral_heatExponential hb]
  unfold gaussianSplineWeight gaussianDamping
  have he : (zeroOffset ρ) ^ 2 / (4 * (b : ℂ)) =
      ((1 / (4 * b) : ℝ) : ℂ) * (zeroOffset ρ) ^ 2 := by
    push_cast
    ring
  rw [he]
  ring

/-- The unnormalized Gaussian of variance `2τ` on the logarithmic scale. -/
def coneHeatWeight (τ y : ℝ) : ℝ := Real.exp (-(4 * τ)⁻¹ * y ^ 2)

/-- The Gaussian-damped kernel has an expression entirely in arithmetic Weil data. -/
theorem gaussianConeKernel_eq_arithmetic_heatAverage {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    gaussianConeKernel τ t =
      (Real.sqrt (4 * Real.pi * τ) : ℂ)⁻¹ *
        ∫ y : ℝ, (coneHeatWeight τ y : ℂ) * arithmeticSplineProfile (t + y) := by
  have hb : 0 < (4 * τ)⁻¹ := inv_pos.mpr (by positivity)
  have h := integral_gaussian_arithmeticSplineProfile hb t
  have ht : (1 : ℝ) / (4 * (4 * τ)⁻¹) = τ := by field_simp [hτ.ne']
  have hm : Real.pi / (4 * τ)⁻¹ = 4 * Real.pi * τ := by rw [div_inv_eq_mul]; ring
  rw [ht, hm] at h
  have hne : (Real.sqrt (4 * Real.pi * τ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  calc
    gaussianConeKernel τ t = (Real.sqrt (4 * Real.pi * τ) : ℂ)⁻¹ *
        ((Real.sqrt (4 * Real.pi * τ) : ℂ) * gaussianConeKernel τ t) := by
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ = _ := by rw [← h]; rfl

/-- The natural-cone coupling is the Gaussian average of the arithmetic mixed difference. -/
theorem gaussianConeCoupling_eq_arithmetic_heatAverage {τ : ℝ} (hτ : 0 < τ)
    (a b : ℝ) (m n : ℕ) :
    gaussianConeCoupling τ a b m n =
      (Real.sqrt (4 * Real.pi * τ) : ℂ)⁻¹ * ∫ y : ℝ, (coneHeatWeight τ y : ℂ) *
        (arithmeticSplineProfile ((m : ℝ) * a + (n : ℝ) * b + y) -
          arithmeticSplineProfile ((m : ℝ) * a + y) -
          arithmeticSplineProfile ((n : ℝ) * b + y) + arithmeticSplineProfile y) := by
  have hb : 0 < (4 * τ)⁻¹ := inv_pos.mpr (by positivity)
  have hi (t : ℝ) : Integrable (fun y : ℝ =>
      (coneHeatWeight τ y : ℂ) * arithmeticSplineProfile (t + y)) :=
    integrable_gaussian_arithmeticSplineProfile hb t
  have h0 : Integrable (fun y : ℝ =>
      (coneHeatWeight τ y : ℂ) * arithmeticSplineProfile y) := by
    simpa only [zero_add] using hi 0
  rw [gaussianConeCoupling_eq_kernel_difference hτ.le]
  simp only [gaussianConeKernel_eq_arithmetic_heatAverage hτ, zero_add]
  have he (y : ℝ) : (coneHeatWeight τ y : ℂ) *
      (arithmeticSplineProfile ((m : ℝ) * a + (n : ℝ) * b + y) -
        arithmeticSplineProfile ((m : ℝ) * a + y) -
        arithmeticSplineProfile ((n : ℝ) * b + y) + arithmeticSplineProfile y) =
      (coneHeatWeight τ y : ℂ) * arithmeticSplineProfile ((m : ℝ) * a + (n : ℝ) * b + y) -
        (coneHeatWeight τ y : ℂ) * arithmeticSplineProfile ((m : ℝ) * a + y) -
        (coneHeatWeight τ y : ℂ) * arithmeticSplineProfile ((n : ℝ) * b + y) +
        (coneHeatWeight τ y : ℂ) * arithmeticSplineProfile y := by ring
  simp_rw [he]
  have hsub₁ := integral_sub (hi ((m : ℝ) * a + (n : ℝ) * b)) (hi ((m : ℝ) * a))
  have hsub₂ := integral_sub ((hi ((m : ℝ) * a + (n : ℝ) * b)).sub
    (hi ((m : ℝ) * a))) (hi ((n : ℝ) * b))
  have hadd := integral_add (((hi ((m : ℝ) * a + (n : ℝ) * b)).sub
    (hi ((m : ℝ) * a))).sub (hi ((n : ℝ) * b))) h0
  simp only [Pi.sub_apply] at hsub₂ hadd
  rw [hadd, hsub₂, hsub₁]
  ring

#print axioms arithmeticSplineProfile_eq_tsum
#print axioms integrable_gaussian_arithmeticSplineProfile
#print axioms integral_gaussian_arithmeticSplineProfile
#print axioms gaussianConeKernel_eq_arithmetic_heatAverage
#print axioms gaussianConeCoupling_eq_arithmetic_heatAverage

end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
