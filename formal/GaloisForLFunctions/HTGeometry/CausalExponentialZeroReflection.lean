import GaloisForLFunctions.HTGeometry.CausalFourierBridge

/-!
# Causal reflection at a Laplace zero

A causal exponential convolution of a negative-half-line profile has a
single exponential tail. Its coefficient is the profile's Laplace value.
A zero of that value therefore keeps the corresponding Blaschke reflection
on the negative half-line. Exponential weighting shifts the kernel rate.
-/

noncomputable section
open Complex Real Set Filter Topology MeasureTheory FourierTransform
open scoped Convolution

namespace RHTower

/-- Reverse the integration variable in the literal convolution integral. -/
theorem causalExponentialConvolution_eq_reversed (a y : ℝ) (f : ℝ → ℂ) :
    (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ∫ u, causalFourierExponential a (y - u) * f u := by
  rw [convolution_def]
  have h := integral_sub_left_eq_self (μ := volume)
    (fun u => causalFourierExponential a (y - u) * f u) y
  convert h using 1
  congr 1
  funext u
  dsimp only [ContinuousLinearMap.mul_apply']
  congr 1
  congr 1
  ring

/-- The causal convolution is the exponentially rescaled lower Laplace integral. -/
theorem causalExponentialConvolution_eq_partial_laplace (a y : ℝ) (f : ℝ → ℂ) :
    (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ((Real.pi : ℂ) * Complex.exp (-(Real.pi * a * y : ℝ))) *
        ∫ u in Iio y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u := by
  rw [causalExponentialConvolution_eq_reversed,
    ← integral_indicator measurableSet_Iio, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  by_cases hu : u ∈ Iio y
  · have huy : y - u ∈ Ioi (0 : ℝ) := by
      change 0 < y - u
      exact sub_pos.mpr hu
    rw [causalFourierExponential, indicator_of_mem huy, indicator_of_mem hu]
    have he : Complex.exp (-((Real.pi * a : ℝ) : ℂ) * ((y - u : ℝ) : ℂ)) =
        Complex.exp (-(Real.pi * a * y : ℝ)) *
          Complex.exp ((Real.pi * a * u : ℝ) : ℂ) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  · have huy : y - u ∉ Ioi (0 : ℝ) := by
      change ¬0 < y - u
      exact not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hu))
    rw [causalFourierExponential, indicator_of_notMem huy, indicator_of_notMem hu,
      zero_mul, mul_zero]

/-- A zero total Laplace integral also gives the upper, anti-causal representation. -/
theorem causalExponentialConvolution_eq_upper_laplace_of_zero (a : ℝ) {f : ℝ → ℂ}
    (hi : Integrable (fun u => Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u))
    (hz : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) = 0) (y : ℝ) :
    (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      -((Real.pi : ℂ) * Complex.exp (-(Real.pi * a * y : ℝ))) *
        ∫ u in Ioi y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u := by
  have hs := integral_add_compl (s := Iio y) measurableSet_Iio hi
  rw [compl_Iio, hz] at hs
  have hs' : (∫ u in Iio y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) +
      (∫ u in Ioi y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) = 0 := by
    simpa only [restrict_Ioi_eq_restrict_Ici] using hs
  have he : (∫ u in Iio y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) =
      -(∫ u in Ioi y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) := by
    calc
      _ = ((∫ u in Iio y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) +
          (∫ u in Ioi y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u)) -
          (∫ u in Ioi y, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) := by ring
      _ = _ := by rw [hs', zero_sub]
  rw [causalExponentialConvolution_eq_partial_laplace, he, mul_neg, neg_mul]

/-- On the positive half-line the entire convolution tail is its Laplace
coefficient times one exponential. No regularity of the profile is needed. -/
theorem causalExponentialConvolution_of_nonneg (a : ℝ) {f : ℝ → ℂ}
    (hf : ∀ u, 0 ≤ u → f u = 0) {y : ℝ} (hy : 0 ≤ y) :
    (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ((Real.pi : ℂ) * Complex.exp (-(Real.pi * a * y : ℝ))) *
        ∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u := by
  rw [causalExponentialConvolution_eq_reversed, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  by_cases hu : 0 ≤ u
  · rw [hf u hu, mul_zero, mul_zero, mul_zero]
  · have huy : y - u ∈ Ioi (0 : ℝ) := by
      change 0 < y - u
      linarith only [hy, lt_of_not_ge hu]
    rw [causalFourierExponential, indicator_of_mem huy]
    have he : Complex.exp (-((Real.pi * a : ℝ) : ℂ) * ((y - u : ℝ) : ℂ)) =
        Complex.exp (-(Real.pi * a * y : ℝ)) *
          Complex.exp ((Real.pi * a * u : ℝ) : ℂ) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring

/-- Vanishing of the Laplace coefficient removes the positive convolution tail. -/
theorem causalExponentialConvolution_support_of_laplace_zero (a : ℝ) {f : ℝ → ℂ}
    (hf : ∀ u, 0 ≤ u → f u = 0)
    (hzero : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) = 0) :
    ∀ y, 0 ≤ y →
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y = 0 := by
  intro y hy
  rw [causalExponentialConvolution_of_nonneg a hf hy, hzero, mul_zero]

/-- A Blaschke reflection at a Laplace zero preserves negative-half-line support. -/
theorem causalBlaschkeStep_support_of_laplace_zero (a : ℝ) {f : ℝ → ℂ}
    (hf : ∀ u, 0 ≤ u → f u = 0)
    (hzero : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) = 0) :
    ∀ y, 0 ≤ y → causalBlaschkeStep a f y = 0 := by
  intro y hy
  rw [causalBlaschkeStep, hf y hy,
    causalExponentialConvolution_support_of_laplace_zero a hf hzero y hy,
    neg_zero, mul_zero, add_zero]

/-- Exponential weighting translates the resolvent rate exactly. -/
theorem exp_mul_causalFourierExponential (a x y : ℝ) :
    Complex.exp (-(Real.pi * x * y : ℝ)) * causalFourierExponential a y =
      causalFourierExponential (a + x) y := by
  unfold causalFourierExponential
  by_cases hy : y ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    calc
      _ = (Real.pi : ℂ) * (Complex.exp (-(Real.pi * x * y : ℝ)) *
          Complex.exp (-((Real.pi * a : ℝ) : ℂ) * y)) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 2
        push_cast
        ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]

end RHTower
