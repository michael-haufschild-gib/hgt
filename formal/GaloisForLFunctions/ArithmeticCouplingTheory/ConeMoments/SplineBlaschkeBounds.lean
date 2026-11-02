import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineDualPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Bounded interval integrals of the spline Blaschke factor

For `r = exp(-2δ) < 1`, the function `((u-r)/(1-r*u))^8`, with `u = exp(2ix)`,
has only nonnegative Fourier frequencies. Multiplication by any positive
frequency therefore admits a bounded primitive. Its explicit binomial
expansion bounds every translated interval integral without shifted-frequency
separation estimates.
-/

open Finset Complex
open scoped Interval
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments


/-- The finite numerator coefficients of the eighth-power Blaschke factor. -/
def splineBlaschkeCoefficient (δ : ℝ) (j : Fin 9) : ℝ :=
  (Nat.choose 8 j.val : ℝ)*(-splineRatio δ)^(8-j.val)

def splineBlaschke (δ x : ℝ) : ℂ :=
  ((phase 2 x-(splineRatio δ : ℂ))/(1-(splineRatio δ : ℂ)*phase 2 x))^8

def splineBlaschkePrimitive (δ v x : ℝ) : ℂ :=
  ∑ j : Fin 9, (splineBlaschkeCoefficient δ j : ℂ)*
    positiveBinomialPrimitive δ (v+2*j.val) x

lemma splineBlaschke_numerator (δ : ℝ) (u : ℂ) :
    ∑ j : Fin 9, (splineBlaschkeCoefficient δ j : ℂ)*u^j.val =
      (u-(splineRatio δ : ℂ))^8 := by
  rw [sub_eq_add_neg, add_pow]
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  simp only [splineBlaschkeCoefficient, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_natCast]
  ring

lemma sum_abs_splineBlaschkeCoefficient (δ : ℝ) :
    ∑ j : Fin 9, |splineBlaschkeCoefficient δ j|=(1+splineRatio δ)^8 := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  simp only [splineBlaschkeCoefficient, abs_mul, abs_pow, abs_neg,
    abs_of_pos (splineRatio_pos δ), abs_of_nonneg (show (0 : ℝ) ≤ (Nat.choose 8 j.val : ℝ) from Nat.cast_nonneg _), one_pow]
  ring

lemma phase_twice_nat (x : ℝ) (j : ℕ) :
    phase (2*j) x=(phase 2 x)^j := by
  simp only [phase]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma hasDerivAt_splineBlaschkePrimitive {δ v : ℝ} (hδ : 0 < δ) (hv : 0 < v)
    (x : ℝ) :
    HasDerivAt (splineBlaschkePrimitive δ v) (phase v x*splineBlaschke δ x) x := by
  have h := HasDerivAt.fun_sum fun j (_ : j ∈ (univ : Finset (Fin 9))) =>
    (hasDerivAt_positiveBinomialPrimitive hδ (by positivity : 0 < v+2*(j.val : ℝ)) x).const_mul (splineBlaschkeCoefficient δ j : ℂ)
  have he : (∑ j : Fin 9, (splineBlaschkeCoefficient δ j : ℂ)*
      (phase (v+2*j.val) x/(1-(splineRatio δ : ℂ)*phase 2 x)^8)) =
      phase v x*splineBlaschke δ x := by
    simp only [phase_freq_add, phase_twice_nat]
    calc
      _ = phase v x*(∑ j : Fin 9, (splineBlaschkeCoefficient δ j : ℂ)*
          (phase 2 x)^j.val)/(1-(splineRatio δ : ℂ)*phase 2 x)^8 := by
        rw [mul_sum, sum_div]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [splineBlaschke_numerator, splineBlaschke, div_pow]; ring
  rw [he] at h
  exact h

lemma norm_splineBlaschkePrimitive_le {δ v : ℝ} (hδ : 0 < δ) (hv : 0 < v)
    (x : ℝ) :
    ‖splineBlaschkePrimitive δ v x‖ ≤ (1+splineRatio δ)^8/v*(1/(1-splineRatio δ)^8) := by
  have hR : 0 ≤ 1/(1-splineRatio δ)^8 := by positivity
  calc
    _ ≤ ∑ j : Fin 9, |splineBlaschkeCoefficient δ j| *
        (1/v*(1/(1-splineRatio δ)^8)) := by
      refine (norm_sum_le _ _).trans ?_
      apply sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (norm_positiveBinomialPrimitive_le hδ (by positivity) x).trans
        (mul_le_mul_of_nonneg_right
          (one_div_le_one_div_of_le hv (le_add_of_nonneg_right (by positivity))) hR)
    _ = _ := by rw [← sum_mul, sum_abs_splineBlaschkeCoefficient]; ring

lemma splineBlaschke_denominator_ne_zero {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    1-(splineRatio δ : ℂ)*phase 2 x ≠ 0 := by
  have hq : ‖(splineRatio δ : ℂ)*phase 2 x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (splineRatio_pos δ),
      phase_norm, mul_one]
    exact splineRatio_lt_one hδ
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hq
  exact lt_irrefl _ hq

lemma continuous_phase (u : ℝ) : Continuous (phase u) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_phase u x).continuousAt

lemma continuous_splineBlaschke {δ : ℝ} (hδ : 0 < δ) : Continuous (splineBlaschke δ) :=
  (((continuous_phase 2).sub continuous_const).div
    (continuous_const.sub (continuous_const.mul (continuous_phase 2)))
    (splineBlaschke_denominator_ne_zero hδ)).pow 8

/-- Every translated interval has the same integral bound; no shifted-frequency gap occurs. -/
theorem norm_integral_phase_splineBlaschke_le {δ v : ℝ} (hδ : 0 < δ) (hv : 0 < v)
    (a b : ℝ) :
    ‖∫ x in a..b, phase v x*splineBlaschke δ x‖ ≤
      2*((1+splineRatio δ)^8/v*(1/(1-splineRatio δ)^8)) := by
  have hi : IntervalIntegrable (fun x => phase v x*splineBlaschke δ x)
      MeasureTheory.volume a b :=
    ((continuous_phase v).mul (continuous_splineBlaschke hδ)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_splineBlaschkePrimitive hδ hv x) hi]
  exact (norm_sub_le _ _).trans (by
    have ha := norm_splineBlaschkePrimitive_le hδ hv a
    have hb := norm_splineBlaschkePrimitive_le hδ hv b
    linarith only [ha, hb])

#print axioms hasDerivAt_splineBlaschkePrimitive
#print axioms norm_integral_phase_splineBlaschke_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
