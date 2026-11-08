import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanCentralMoments
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanCentralJet
import GaloisForLFunctions.RHTower.RealJetsOfHolomorphic

/-!
# Central Mellin jets as physical Narain moments

Fourier differentiation identifies every central complex jet with an absolutely convergent physical logarithmic moment, including the first-moment height law.
-/

open Complex RHTower MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Real derivatives along a complex line equal its complex jets times the line-direction powers. -/
private theorem iteratedDeriv_complexLine {F : ℂ → ℂ} {a : ℂ}
    (hF : ∀ x : ℝ, AnalyticAt ℂ F (a * (x : ℂ))) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => F (a * (t : ℂ))) x =
      a ^ n * iteratedDeriv n F (a * (x : ℂ)) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t : ℝ => F (a * (t : ℂ))) =
        fun t : ℝ => a ^ n * iteratedDeriv n F (a * (t : ℂ)) := funext ih
    rw [heq]
    have hk := GaloisForLFunctions.RHTower.analyticAt_iteratedDeriv_complex (hF x) n
    have hd := hk.differentiableAt.hasDerivAt.comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).const_mul a)
    have hr := hd.comp_ofReal.const_mul (a ^ n)
    rw [hr.deriv, iteratedDeriv_succ, pow_succ]
    ring

/-- Every tangential frequency derivative equals its actual complex Mellin jet. -/
theorem iteratedDeriv_narainMeanBoundaryFrequency (Y Z : Height) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (narainMeanBoundaryFrequency Y Z) t =
      (2 * (Real.pi : ℂ) * I) ^ n * iteratedDeriv n (narainMellinMean Y Z)
        ((2 * (Real.pi : ℂ) * I) * (t : ℂ)) := by
  have hfreq : narainMeanBoundaryFrequency Y Z =
      fun t : ℝ => narainMellinMean Y Z ((2 * (Real.pi : ℂ) * I) * (t : ℂ)) := by
    funext t
    unfold narainMeanBoundaryFrequency
    congr 1
    ring
  rw [hfreq]
  have hF : ∀ x : ℝ, AnalyticAt ℂ (narainMellinMean Y Z)
      ((2 * (Real.pi : ℂ) * I) * (x : ℂ)) := by
    intro x
    apply analyticAt_narainMellinMean_of_nonneg_re Y Z
    · simp [Complex.mul_re, Complex.mul_im]
    · intro h
      have hr := congrArg Complex.re h
      norm_num [Complex.mul_re, Complex.mul_im] at hr
  exact iteratedDeriv_complexLine hF n t

/-- At zero the line-direction factor is the only change in the central jet. -/
theorem iteratedDeriv_narainMeanBoundaryFrequency_zero (Y Z : Height) (n : ℕ) :
    iteratedDeriv n (narainMeanBoundaryFrequency Y Z) 0 =
      (2 * (Real.pi : ℂ) * I) ^ n * iteratedDeriv n (narainMellinMean Y Z) 0 := by
  simpa only [Complex.ofReal_zero, mul_zero] using iteratedDeriv_narainMeanBoundaryFrequency Y Z n 0

/-- Fourier inversion identifies the actual clock and frequency functions pointwise. -/
theorem fourier_narainMeanClockSchwartz (Y Z : Height) :
    FourierTransform.fourier (narainMeanClockSchwartz Y Z : ℝ → ℂ) =
      narainMeanBoundaryFrequency Y Z := by
  have hH : (narainMeanClockSchwartz Y Z : ℝ → ℂ) =
      FourierTransform.fourierInv (narainMeanBoundaryFrequency Y Z) := by
    funext L
    rw [narainMeanClockSchwartz, GaloisForLFunctions.HTGeometry.schwartzScale_apply,
      neg_one_mul, narainMeanFourierSchwartz_apply, Real.fourierInv_eq_fourier_neg]
    rfl
  rw [hH]
  have hG : Integrable (narainMeanBoundaryFrequency Y Z) := by
    apply (integrable_narainMeanBoundaryFrequency_moment Y Z 0).mono'
      (continuous_narainMeanBoundaryFrequency Y Z).aestronglyMeasurable
    filter_upwards [] with t
    simp
  have hF : Integrable (FourierTransform.fourier (narainMeanBoundaryFrequency Y Z)) :=
    (narainMeanFourierSchwartz Y Z).integrable
  exact (continuous_narainMeanBoundaryFrequency Y Z).fourier_fourierInv_eq hG hF

/-- Every central complex jet is an absolutely convergent logarithmic-clock moment. -/
theorem iteratedDeriv_narainMellinMean_zero_eq_clock_moment (Y Z : Height) (n : ℕ) :
    iteratedDeriv n (narainMellinMean Y Z) 0 =
      ∫ L : ℝ, ((-L : ℝ) : ℂ) ^ n * narainMeanClockSchwartz Y Z L := by
  have hmoment (m : ℕ) : Integrable (fun L : ℝ => L ^ m • narainMeanClockSchwartz Y Z L) := by
    apply ((narainMeanClockSchwartz Y Z).integrable_pow_mul volume m).mono'
      ((continuous_id.pow m).smul (narainMeanClockSchwartz Y Z).continuous).aestronglyMeasurable
    filter_upwards [] with L
    rw [norm_smul, norm_pow]
  have hd := congrFun (Real.iteratedDeriv_fourier (N := ⊤)
    (fun m _ => hmoment m) (n := n) le_top) 0
  rw [fourier_narainMeanClockSchwartz, iteratedDeriv_narainMeanBoundaryFrequency_zero,
    GaloisForLFunctions.HTGeometry.fourier_zero_eq_integral] at hd
  have ha : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  apply mul_left_cancel₀ (pow_ne_zero n ha)
  calc
    _ = ∫ L : ℝ, (-2 * (Real.pi : ℂ) * I * (L : ℂ)) ^ n • narainMeanClockSchwartz Y Z L := hd
    _ = (2 * (Real.pi : ℂ) * I) ^ n *
        ∫ L : ℝ, ((-L : ℝ) : ℂ) ^ n * narainMeanClockSchwartz Y Z L := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with L
      rw [smul_eq_mul, show -2 * (Real.pi : ℂ) * I * (L : ℂ) =
        (2 * (Real.pi : ℂ) * I) * ((-L : ℝ) : ℂ) by push_cast; ring, mul_pow]
      ring

/-- Every physical logarithmic moment equals its exact central Mellin derivative. -/
theorem integral_narainMeanMomentDensity_eq_jet (Y Z : Height) (n : ℕ) :
    (∫ y in Set.Ioi (0 : ℝ), narainMeanMomentDensity Y Z n y) =
      iteratedDeriv n (narainMellinMean Y Z) 0 := by
  rw [integral_narainMeanMomentDensity_eq_clock, iteratedDeriv_narainMellinMean_zero_eq_clock_moment]

/-- The first physical moment factors into the two exact target-height defects. -/
theorem integral_narainMeanMomentDensity_one (Y Z : Height) :
    (∫ y in Set.Ioi (0 : ℝ), narainMeanMomentDensity Y Z 1 y) =
      4 * (Y.val : ℂ) ^ (1 / 2 : ℂ) * (Z.val : ℂ) ^ (1 / 2 : ℂ) *
        (2 - 4 * deriv xi 1 - Complex.log (Y.val : ℂ)) *
          (2 - 4 * deriv xi 1 - Complex.log (Z.val : ℂ)) := by
  rw [integral_narainMeanMomentDensity_eq_jet]
  simpa only [iteratedDeriv_one] using narainMellinMean_deriv_zero Y Z

/-- At fixed target product, the first moment varies quadratically with logarithmic height imbalance. -/
theorem integral_narainMeanMomentDensity_one_product_imbalance (Y Z : Height) :
    (∫ y in Set.Ioi (0 : ℝ), narainMeanMomentDensity Y Z 1 y) =
      4 * ((Y.val * Z.val : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        ((2 - 4 * deriv xi 1 - Complex.log ((Y.val * Z.val : ℝ) : ℂ) / 2) ^ 2 -
          ((Complex.log (Y.val : ℂ) - Complex.log (Z.val : ℂ)) / 2) ^ 2) := by
  have hlog : Complex.log ((Y.val * Z.val : ℝ) : ℂ) =
      Complex.log (Y.val : ℂ) + Complex.log (Z.val : ℂ) := by
    rw [← Complex.ofReal_log (mul_pos Y.property Z.property).le,
      ← Complex.ofReal_log Y.property.le, ← Complex.ofReal_log Z.property.le,
      Real.log_mul Y.property.ne' Z.property.ne', Complex.ofReal_add]
  rw [integral_narainMeanMomentDensity_one, hlog, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Y.property.le Z.property.le]
  ring

#print axioms iteratedDeriv_narainMeanBoundaryFrequency
#print axioms fourier_narainMeanClockSchwartz
#print axioms iteratedDeriv_narainMellinMean_zero_eq_clock_moment
#print axioms integral_narainMeanMomentDensity_eq_jet
#print axioms integral_narainMeanMomentDensity_one
#print axioms integral_narainMeanMomentDensity_one_product_imbalance
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
