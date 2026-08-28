import GaloisForLFunctions.RHTower.BesselJZeroSecondSolution
import GaloisForLFunctions.RHTower.BesselJOneRecurrence
import GaloisForLFunctions.HTGeometry.MixedEvenTrigMoments
import GaloisForLFunctions.HTGeometry.ClockSeriesIntegral
import GaloisForLFunctions.HTGeometry.CentralBinomialRoot

/-!
# Oscillatory Bessel realization of the Route-T residual Borel kernel

The second-factorial kernel on its negative real ray is exactly `J₀(2√r)`.  The flat Bessel
origin then turns adjacent prime-log heights into a linear gap bound, which is the missing
source-summable majorant for safe-side Borel--Laplace reconstruction.
-/

open Complex MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

def secondFactorialBorelKernel (z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ k / ((k.factorial : ℂ) ^ 2)

private def besselCosineSeriesTerm (u : ℝ) (k : ℕ) (theta : ℝ) : ℂ :=
  (-1 : ℂ) ^ k * (((u * Real.cos theta : ℝ) : ℂ) ^ (2 * k)) /
    ((2 * k).factorial : ℂ)

private theorem continuous_besselCosineSeriesTerm (u : ℝ) (k : ℕ) :
    Continuous (besselCosineSeriesTerm u k) := by
  unfold besselCosineSeriesTerm
  fun_prop

private theorem norm_besselCosineSeriesTerm_le (u : ℝ) (k : ℕ) (theta : ℝ) :
    ‖besselCosineSeriesTerm u k theta‖ ≤
      |u| ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  rw [besselCosineSeriesTerm, norm_div, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    Complex.norm_natCast]
  norm_num
  have hc := Real.abs_cos_le_one theta
  have hu : 0 ≤ |u| := abs_nonneg u
  have hfac : 0 ≤ ((2 * k).factorial : ℝ) := by positivity
  gcongr
  nlinarith [abs_nonneg (Real.cos theta)]

private theorem summable_besselCosineSeriesMajorant (u : ℝ) :
    Summable (fun k : ℕ => |u| ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
  have hs := (Complex.hasSum_cos ((|u| : ℝ) : ℂ)).summable.norm
  simpa [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (abs_nonneg u), Complex.norm_natCast] using hs

private theorem tsum_besselCosineSeriesTerm (u theta : ℝ) :
    (∑' k : ℕ, besselCosineSeriesTerm u k theta) =
      ((Real.cos (u * Real.cos theta) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cos]
  simpa [besselCosineSeriesTerm] using
    (Complex.hasSum_cos (((u * Real.cos theta : ℝ) : ℂ))).tsum_eq

private theorem integral_ofReal_eq
    {α : Type*} [MeasurableSpace α] {mu : Measure α} {f : α → ℝ}
    (hf : Integrable f mu) :
    (∫ x, ((f x : ℝ) : ℂ) ∂mu) = ((∫ x, f x ∂mu : ℝ) : ℂ) := by
  rw [← Complex.ofRealCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hf]
  rfl

private theorem intervalIntegral_ofReal_eq
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, ((f x : ℝ) : ℂ)) =
      (((∫ x in a..b, f x : ℝ)) : ℂ) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hi := intervalIntegrable_iff.mp hf
  rw [uIoc_of_le hab] at hi
  exact integral_ofReal_eq hi

private theorem integral_besselCosineSeriesTerm (u : ℝ) (k : ℕ) :
    (∫ theta in (0 : ℝ)..Real.pi / 2, besselCosineSeriesTerm u k theta) =
      (-1 : ℂ) ^ k * (u : ℂ) ^ (2 * k) / ((2 * k).factorial : ℂ) *
        (((Real.pi / 2) * normalizedCentralBinom k : ℝ) : ℂ) := by
  rw [show besselCosineSeriesTerm u k = fun theta : ℝ =>
      ((-1 : ℂ) ^ k * (u : ℂ) ^ (2 * k) / ((2 * k).factorial : ℂ)) *
        ((Real.cos theta ^ (2 * k) : ℝ) : ℂ) by
    funext theta
    simp only [besselCosineSeriesTerm]
    push_cast
    rw [mul_pow]
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [show (∫ theta in (0 : ℝ)..Real.pi / 2,
      ((Real.cos theta ^ (2 * k) : ℝ) : ℂ)) =
      (((∫ theta in (0 : ℝ)..Real.pi / 2,
        Real.cos theta ^ (2 * k)) : ℝ) : ℂ) by
    exact intervalIntegral_ofReal_eq (by positivity)
      ((Real.continuous_cos.pow (2 * k)).intervalIntegrable _ _)]
  rw [integral_cos_pow_even_zero_pi_div_two]

private theorem normalizedCentralBinom_div_evenFactorial (k : ℕ) :
    ((normalizedCentralBinom k : ℝ) : ℂ) / ((2 * k).factorial : ℂ) =
      1 / ((4 : ℂ) ^ k * ((k.factorial : ℂ) ^ 2)) := by
  rw [normalizedCentralBinom]
  push_cast
  have h4 : (4 : ℂ) ^ k ≠ 0 := by norm_num
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h2k : ((2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast (2 * k).factorial_ne_zero
  have hid := GaloisForLFunctions.HTGeometry.centralBinom_mul_factorial_sq k
  field_simp [h4, hk, h2k]
  norm_cast
  simpa [pow_two] using hid

theorem ofReal_besselJ0_eq_secondFactorial_series (u : ℝ) :
    ((besselJ0 u : ℝ) : ℂ) =
      ∑' k : ℕ,
        (-1 : ℂ) ^ k * (u : ℂ) ^ (2 * k) /
          ((4 : ℂ) ^ k * ((k.factorial : ℂ) ^ 2)) := by
  rw [besselJ0_cos_form]
  push_cast
  rw [show (((∫ theta in (0 : ℝ)..Real.pi / 2,
      Real.cos (u * Real.cos theta)) : ℝ) : ℂ) =
      ∫ theta in (0 : ℝ)..Real.pi / 2,
        ((Real.cos (u * Real.cos theta) : ℝ) : ℂ) by
    symm
    exact intervalIntegral_ofReal_eq (by positivity)
      ((by fun_prop : Continuous (fun theta : ℝ =>
        Real.cos (u * Real.cos theta))).intervalIntegrable _ _)]
  rw [show (∫ theta in (0 : ℝ)..Real.pi / 2,
      ((Real.cos (u * Real.cos theta) : ℝ) : ℂ)) =
      ∑' k : ℕ, ∫ theta in (0 : ℝ)..Real.pi / 2,
        besselCosineSeriesTerm u k theta by
    rw [GaloisForLFunctions.HTGeometry.tsum_intervalIntegral_of_bound
      (continuous_besselCosineSeriesTerm u)
      (fun k theta _ => norm_besselCosineSeriesTerm_le u k theta)
      (summable_besselCosineSeriesMajorant u)]
    apply intervalIntegral.integral_congr
    intro theta _
    exact (tsum_besselCosineSeriesTerm u theta).symm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [integral_besselCosineSeriesTerm]
  push_cast
  calc
    2 / (Real.pi : ℂ) *
        ((-1 : ℂ) ^ k * (u : ℂ) ^ (2 * k) / ((2 * k).factorial : ℂ) *
          ((Real.pi : ℂ) / 2 * (normalizedCentralBinom k : ℂ))) =
        (-1 : ℂ) ^ k * (u : ℂ) ^ (2 * k) *
          ((normalizedCentralBinom k : ℂ) / ((2 * k).factorial : ℂ)) := by
      field_simp [Real.pi_ne_zero]
    _ = _ := by
      rw [normalizedCentralBinom_div_evenFactorial]
      ring

theorem secondFactorialBorelKernel_neg_real_eq_besselJ0
    {r : ℝ} (hr : 0 ≤ r) :
    secondFactorialBorelKernel (-(r : ℂ)) =
      ((besselJ0 (2 * Real.sqrt r) : ℝ) : ℂ) := by
  rw [secondFactorialBorelKernel,
    ofReal_besselJ0_eq_secondFactorial_series]
  apply tsum_congr
  intro k
  have hs : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr
  have hsq : (2 * Real.sqrt r) ^ 2 = 4 * r := by nlinarith
  have hu : (((2 * Real.sqrt r : ℝ) : ℂ) ^ (2 * k)) / (4 : ℂ) ^ k =
      (r : ℂ) ^ k := by
    calc
      (((2 * Real.sqrt r : ℝ) : ℂ) ^ (2 * k)) / (4 : ℂ) ^ k =
          ((((2 * Real.sqrt r : ℝ) : ℂ) ^ 2) ^ k) / (4 : ℂ) ^ k := by
            rw [pow_mul]
      _ = (((4 : ℂ) * (r : ℂ)) ^ k) / (4 : ℂ) ^ k := by
            congr 2
            exact_mod_cast hsq
      _ = (r : ℂ) ^ k := by
            rw [mul_pow]
            have h4 : (4 : ℂ) ^ k ≠ 0 := by norm_num
            field_simp
  rw [neg_pow, ← hu]
  ring

/-- The flat origin makes the Bessel edge Lipschitz in squared frequency. -/
theorem abs_besselJ0_sub_le_sq_sub
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    |besselJ0 u - besselJ0 v| ≤ (v ^ 2 - u ^ 2) / 2 := by
  have hv : 0 ≤ v := hu.trans huv
  have hdiff : ∀ theta ∈ uIcc v u, DifferentiableAt ℝ besselJ0 theta := by
    intro theta _
    exact (hasDerivAt_besselJ0 theta).differentiableAt
  have hbound : ∀ theta ∈ uIcc v u, ‖deriv besselJ0 theta‖ ≤ v / 2 := by
    intro theta htheta
    rw [(hasDerivAt_besselJ0 theta).deriv, Real.norm_eq_abs]
    rw [show |besselJ0Deriv theta| = |besselJ1 theta| by
      simp [besselJ1]]
    refine (abs_besselJ1_le theta).trans ?_
    have hmem : theta ∈ Icc u v := by
      rw [uIcc_of_ge huv] at htheta
      exact htheta
    have htheta0 : 0 ≤ theta := hu.trans hmem.1
    rw [abs_of_nonneg htheta0]
    linarith [hmem.2]
  have h := (convex_uIcc v u).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr huv)] at h
  have h' : |besselJ0 u - besselJ0 v| ≤ v / 2 * (v - u) := by
    convert h using 1
    ring
  calc
    |besselJ0 u - besselJ0 v| ≤ v / 2 * (v - u) := h'
    _ ≤ (v ^ 2 - u ^ 2) / 2 := by
      nlinarith

theorem norm_secondFactorialBorelKernel_neg_mul_sub_le
    {h H q : ℝ} (hh : 0 ≤ h) (hH : h ≤ H) (hq : 0 ≤ q) :
    ‖secondFactorialBorelKernel (-((h * q : ℝ) : ℂ)) -
        secondFactorialBorelKernel (-((H * q : ℝ) : ℂ))‖ ≤
      2 * (H - h) * q := by
  have hhq : 0 ≤ h * q := mul_nonneg hh hq
  have hH0 : 0 ≤ H := hh.trans hH
  have hHq : 0 ≤ H * q := mul_nonneg hH0 hq
  have hmul : h * q ≤ H * q := mul_le_mul_of_nonneg_right hH hq
  rw [secondFactorialBorelKernel_neg_real_eq_besselJ0 hhq,
    secondFactorialBorelKernel_neg_real_eq_besselJ0 hHq,
    ← ofReal_sub, norm_real, Real.norm_eq_abs]
  have hsqrt := Real.sqrt_le_sqrt hmul
  have hb := abs_besselJ0_sub_le_sq_sub
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 2))
  calc
    |besselJ0 (2 * Real.sqrt (h * q)) -
        besselJ0 (2 * Real.sqrt (H * q))| ≤
        ((2 * Real.sqrt (H * q)) ^ 2 -
          (2 * Real.sqrt (h * q)) ^ 2) / 2 := hb
    _ = 2 * (H - h) * q := by
      nlinarith [Real.sq_sqrt hhq, Real.sq_sqrt hHq]

end

end RHTower
