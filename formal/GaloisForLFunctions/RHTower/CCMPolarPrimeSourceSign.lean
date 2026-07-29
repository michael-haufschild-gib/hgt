import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The corrected polar source sign and its exact Fourier multiplier

This file formalizes the source-side calculus behind the polar term in the finite-aperture CCM
symbol.  The local polar potential has second derivative `-2 cosh(t/2)`, so the distributional
kernel `-r₀''` is the positive kernel `2 cosh(t/2)`.  Its compact-aperture Fourier transform, in
the convention `exp(i ξ t)`, is exactly `polarMultiplier`.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- The local polar potential in the screw-function normalization. -/
def ccmPolarPotential (t : ℝ) : ℝ :=
  -8 * (Real.cosh (t / 2) - 1)

/-- First derivative of the local polar potential. -/
theorem hasDerivAt_ccmPolarPotential (t : ℝ) :
    HasDerivAt ccmPolarPotential (-4 * Real.sinh (t / 2)) t := by
  have h :=
    (((Real.hasDerivAt_cosh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).sub_const 1
      |>.const_mul (-8))
  have hfun :
      ccmPolarPotential = fun u : ℝ => -8 * (Real.cosh (u / 2) - 1) := by
    funext u
    rfl
  rw [hfun]
  apply h.congr_deriv
  ring

/-- Second derivative of the local polar potential. -/
theorem hasDerivAt_ccmPolarPotential_derivative (t : ℝ) :
    HasDerivAt (fun u : ℝ => -4 * Real.sinh (u / 2))
      (-2 * Real.cosh (t / 2)) t := by
  have h :=
    ((Real.hasDerivAt_sinh (t / 2)).comp t
      ((hasDerivAt_id t).div_const 2)).const_mul (-4)
  apply h.congr_deriv
  ring

/-- The distributional sign is forced: `-r₀''` is the positive polar kernel. -/
theorem neg_ccmPolarPotential_secondDerivative (t : ℝ) :
    -(-2 * Real.cosh (t / 2)) = 2 * Real.cosh (t / 2) := by
  ring

/-- The signed source derivative at a difference variable is exactly the existing polar kernel. -/
theorem neg_ccmPolarPotential_secondDerivative_eq_polarKernel (x y : ℝ) :
    -(-2 * Real.cosh ((x - y) / 2)) = polarKernel x y := by
  rw [polarKernel]
  ring

/-- A primitive for the positive-lag cosine transform of the polar source. -/
def polarCosinePrimitive (ξ t : ℝ) : ℝ :=
  (Real.sinh (t / 2) * Real.cos (ξ * t) +
      2 * ξ * Real.cosh (t / 2) * Real.sin (ξ * t)) /
    (ξ ^ 2 + 1 / 4)

/-- The primitive differentiates to `2 cosh(t/2) cos(ξt)`. -/
theorem hasDerivAt_polarCosinePrimitive (ξ t : ℝ) :
    HasDerivAt (polarCosinePrimitive ξ)
      (2 * Real.cosh (t / 2) * Real.cos (ξ * t)) t := by
  have hden : ξ ^ 2 + 1 / 4 ≠ 0 := by positivity
  have hsinh : HasDerivAt (fun u : ℝ => Real.sinh (u / 2))
      ((1 / 2 : ℝ) * Real.cosh (t / 2)) t := by
    apply ((Real.hasDerivAt_sinh (t / 2)).comp t
      ((hasDerivAt_id t).div_const 2)).congr_deriv
    ring
  have hcosh : HasDerivAt (fun u : ℝ => Real.cosh (u / 2))
      ((1 / 2 : ℝ) * Real.sinh (t / 2)) t := by
    apply ((Real.hasDerivAt_cosh (t / 2)).comp t
      ((hasDerivAt_id t).div_const 2)).congr_deriv
    ring
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (ξ * u))
      (-ξ * Real.sin (ξ * t)) t := by
    apply ((Real.hasDerivAt_cos (ξ * t)).comp t
      ((hasDerivAt_id t).const_mul ξ)).congr_deriv
    ring
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (ξ * u))
      (ξ * Real.cos (ξ * t)) t := by
    apply ((Real.hasDerivAt_sin (ξ * t)).comp t
      ((hasDerivAt_id t).const_mul ξ)).congr_deriv
    ring
  have hnum := (hsinh.mul hcos).add ((hcosh.mul hsin).const_mul (2 * ξ))
  rw [show polarCosinePrimitive ξ = fun u : ℝ =>
      (Real.sinh (u / 2) * Real.cos (ξ * u) +
        2 * ξ * (Real.cosh (u / 2) * Real.sin (ξ * u))) /
          (ξ ^ 2 + 1 / 4) by
    funext u
    rw [polarCosinePrimitive]
    ring]
  apply (hnum.div_const (ξ ^ 2 + 1 / 4)).congr_deriv
  field_simp [hden]
  ring

/-- Exact positive-lag cosine transform of the polar source. -/
theorem integral_polarCosineSource_Ioc
    {a ξ : ℝ} (ha : 0 ≤ a) :
    (∫ h in Ioc (0 : ℝ) (2 * a),
      2 * Real.cosh (h / 2) * Real.cos (ξ * h)) =
      Real.sinh a * Real.cos (2 * a * ξ) /
          (ξ ^ 2 + 1 / 4) +
        2 * ξ * Real.cosh a * Real.sin (2 * a * ξ) /
          (ξ ^ 2 + 1 / 4) := by
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * a)]
  have hint : IntervalIntegrable
      (fun h : ℝ => 2 * Real.cosh (h / 2) * Real.cos (ξ * h)) volume 0 (2 * a) := by
    exact ((continuous_const.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable
          0 (2 * a)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun h _ => hasDerivAt_polarCosinePrimitive ξ h)
    hint]
  rw [polarCosinePrimitive, polarCosinePrimitive]
  norm_num
  rw [show ξ * (2 * a) = 2 * a * ξ by ring]
  ring

/-- The even compact-aperture cosine transform is the corrected rational multiplier. -/
theorem polarMultiplier_eq_cosineTransform
    {a ξ : ℝ} (ha : 0 ≤ a) :
    polarMultiplier a ξ =
      2 * ∫ h in Ioc (0 : ℝ) (2 * a),
        2 * Real.cosh (h / 2) * Real.cos (ξ * h) := by
  rw [integral_polarCosineSource_Ioc ha, polarMultiplier]
  ring

/-- The sine part of the symmetric polar transform vanishes by oddness. -/
theorem integral_polarSineSource_symmetric (a ξ : ℝ) :
    (∫ h in (-(2 * a))..(2 * a),
      2 * Real.cosh (h / 2) * Real.sin (ξ * h)) = 0 := by
  let f : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2) * Real.sin (ξ * h)
  have hodd : ∀ h : ℝ, f (-h) = -f h := by
    intro h
    simp only [f, neg_div, Real.cosh_neg, mul_neg, Real.sin_neg]
  have hcomp := intervalIntegral.integral_comp_neg
    (a := -(2 * a)) (b := 2 * a) f
  simp only [neg_neg] at hcomp
  have hneg : (∫ h in (-(2 * a))..(2 * a), f (-h)) =
      -(∫ h in (-(2 * a))..(2 * a), f h) := by
    rw [intervalIntegral.integral_congr (fun h _ => hodd h), intervalIntegral.integral_neg]
  rw [hneg] at hcomp
  linarith

/-- Full compact-aperture Fourier transform in the convention `exp(i ξ t)`. -/
def polarFourierTransform (a ξ : ℝ) : ℂ :=
  ∫ h in (-(2 * a))..(2 * a),
    (2 * Real.cosh (h / 2) : ℂ) *
      Complex.exp (((ξ * h : ℝ) : ℂ) * Complex.I)

/-- The full Fourier transform is real and equals the corrected polar multiplier. -/
theorem polarFourierTransform_eq_polarMultiplier
    {a ξ : ℝ} (ha : 0 ≤ a) :
    polarFourierTransform a ξ = (polarMultiplier a ξ : ℂ) := by
  have hcosEven :
      (∫ h in (-(2 * a))..(2 * a),
        2 * Real.cosh (h / 2) * Real.cos (ξ * h)) =
      2 * ∫ h in (0 : ℝ)..(2 * a),
        2 * Real.cosh (h / 2) * Real.cos (ξ * h) := by
    let g : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2) * Real.cos (ξ * h)
    have heven : ∀ h : ℝ, g (-h) = g h := by
      intro h
      simp only [g, neg_div, Real.cosh_neg, mul_neg, Real.cos_neg]
    have hg : Continuous g :=
      (continuous_const.mul
        (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    have hgLeft : IntervalIntegrable g volume (-(2 * a)) 0 :=
      hg.intervalIntegrable (-(2 * a)) 0
    have hgRight : IntervalIntegrable g volume 0 (2 * a) :=
      hg.intervalIntegrable 0 (2 * a)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      hgLeft hgRight (b := 0)]
    have hcomp := intervalIntegral.integral_comp_neg
      (a := (0 : ℝ)) (b := 2 * a) g
    simp only [neg_zero] at hcomp
    rw [intervalIntegral.integral_congr (fun h _ => heven h)] at hcomp
    rw [hcomp]
    ring
  rw [polarFourierTransform]
  have hexp : ∀ h : ℝ,
      (2 * Real.cosh (h / 2) : ℂ) *
          Complex.exp (((ξ * h : ℝ) : ℂ) * Complex.I) =
        (2 * Real.cosh (h / 2) * Real.cos (ξ * h) : ℝ) +
          (2 * Real.cosh (h / 2) * Real.sin (ξ * h) : ℝ) * Complex.I := by
    intro h
    rw [Complex.exp_mul_I]
    push_cast
    ring
  have hcosInt : IntervalIntegrable
      (fun h : ℝ => (2 : ℂ) * (Real.cosh (h / 2) : ℂ) * (Real.cos (ξ * h) : ℂ))
      volume (-(2 * a)) (2 * a) := by
    have hc : Continuous
        (fun h : ℝ => (2 : ℂ) * (Real.cosh (h / 2) : ℂ) * (Real.cos (ξ * h) : ℂ)) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume) (-(2 * a)) (2 * a)
  have hsinInt : IntervalIntegrable
      (fun h : ℝ => (2 : ℂ) * (Real.cosh (h / 2) : ℂ) *
        (Real.sin (ξ * h) : ℂ) * Complex.I)
      volume (-(2 * a)) (2 * a) := by
    have hc : Continuous
        (fun h : ℝ => (2 : ℂ) * (Real.cosh (h / 2) : ℂ) *
          (Real.sin (ξ * h) : ℂ) * Complex.I) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume) (-(2 * a)) (2 * a)
  have hcastCos : ∀ h : ℝ,
      (2 * Real.cosh (h / 2) * Real.cos (ξ * h) : ℝ) =
        (2 : ℂ) * (Real.cosh (h / 2) : ℂ) * (Real.cos (ξ * h) : ℂ) := by
    intro h
    push_cast
    rfl
  have hcastSinBase : ∀ h : ℝ,
      (2 * Real.cosh (h / 2) * Real.sin (ξ * h) : ℝ) =
        (2 : ℂ) * (Real.cosh (h / 2) : ℂ) * (Real.sin (ξ * h) : ℂ) := by
    intro h
    push_cast
    rfl
  have hcastSin : ∀ h : ℝ,
      (2 * Real.cosh (h / 2) * Real.sin (ξ * h) : ℝ) * Complex.I =
        (2 : ℂ) * (Real.cosh (h / 2) : ℂ) *
          (Real.sin (ξ * h) : ℂ) * Complex.I := by
    intro h
    rw [hcastSinBase h]
  rw [intervalIntegral.integral_congr (fun h _ => hexp h)]
  rw [intervalIntegral.integral_congr (fun h _ => by
    rw [hcastCos h, hcastSin h])]
  rw [intervalIntegral.integral_add hcosInt hsinInt,
    intervalIntegral.integral_mul_const]
  let fcos : ℝ → ℝ := fun h =>
    2 * Real.cosh (h / 2) * Real.cos (ξ * h)
  let fsin : ℝ → ℝ := fun h =>
    2 * Real.cosh (h / 2) * Real.sin (ξ * h)
  let Icos : ℝ := ∫ h in (-(2 * a))..(2 * a), fcos h
  let Isin : ℝ := ∫ h in (-(2 * a))..(2 * a), fsin h
  have hcosCastEq :
      (∫ h in (-(2 * a))..(2 * a),
        (2 : ℂ) * (Real.cosh (h / 2) : ℂ) * (Real.cos (ξ * h) : ℂ)) =
      (Icos : ℂ) := by
    calc
      (∫ h in (-(2 * a))..(2 * a),
          (2 : ℂ) * (Real.cosh (h / 2) : ℂ) * (Real.cos (ξ * h) : ℂ)) =
          ∫ h in (-(2 * a))..(2 * a), (fcos h : ℂ) := by
            apply intervalIntegral.integral_congr
            intro h _
            exact (hcastCos h).symm
      _ = (Icos : ℂ) := by
        simp only [Icos]
        exact intervalIntegral.integral_ofReal
  have hsinCastEq :
      (∫ h in (-(2 * a))..(2 * a),
        (2 : ℂ) * (Real.cosh (h / 2) : ℂ) * (Real.sin (ξ * h) : ℂ)) =
      (Isin : ℂ) := by
    calc
      (∫ h in (-(2 * a))..(2 * a),
          (2 : ℂ) * (Real.cosh (h / 2) : ℂ) * (Real.sin (ξ * h) : ℂ)) =
          ∫ h in (-(2 * a))..(2 * a), (fsin h : ℂ) := by
            apply intervalIntegral.integral_congr
            intro h _
            exact (hcastSinBase h).symm
      _ = (Isin : ℂ) := by
        simp only [Isin]
        exact intervalIntegral.integral_ofReal
  have hfsin : Isin = 0 := by
    change (∫ h in (-(2 * a))..(2 * a), fsin h) = 0
    simpa only [fsin] using integral_polarSineSource_symmetric a ξ
  have hfcos : Icos =
      2 * ∫ h in (0 : ℝ)..(2 * a),
        2 * Real.cosh (h / 2) * Real.cos (ξ * h) := by
    change (∫ h in (-(2 * a))..(2 * a), fcos h) = _
    simpa only [fcos] using hcosEven
  rw [hcosCastEq, hsinCastEq, hfsin, hfcos]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  norm_cast
  rw [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * a),
    ← polarMultiplier_eq_cosineTransform ha]

end RHTower
