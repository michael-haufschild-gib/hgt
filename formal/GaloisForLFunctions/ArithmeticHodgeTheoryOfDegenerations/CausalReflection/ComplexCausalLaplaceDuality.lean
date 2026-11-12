import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexCausalLaplaceWeight

/-!
# Two-sided representations of a complex causal resolvent

A vanishing total Laplace coefficient identifies the lower-tail causal
formula with a negative upper-tail formula. The latter supplies the moment
law when exponential weighting makes the original causal kernel grow.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry

private theorem complexCausalConvolution_eq_reversed (z : ℂ) (y : ℝ) (f : ℝ → ℂ) :
    (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ∫ u, complexRateCausalKernel z (y - u) * f u := by
  rw [convolution_def]
  have h := integral_sub_left_eq_self (μ := volume)
    (fun u => complexRateCausalKernel z (y - u) * f u) y
  convert h using 1
  congr 1
  funext u
  dsimp only [ContinuousLinearMap.mul_apply']
  congr 1
  congr 1
  ring

/-- The actual complex resolvent is the rescaled lower Laplace tail. -/
theorem complexCausalConvolution_eq_partial_laplace (z : ℂ) (y : ℝ) (f : ℝ → ℂ) :
    (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ((Real.pi : ℂ) * Complex.exp ((-z) * (y : ℂ))) *
        ∫ u in Iio y, Complex.exp (z * (u : ℂ)) * f u := by
  rw [complexCausalConvolution_eq_reversed,
    ← integral_indicator measurableSet_Iio, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  by_cases hu : u ∈ Iio y
  · have huy : y - u ∈ Ioi (0 : ℝ) := by
      change 0 < y - u
      exact sub_pos.mpr hu
    rw [complexRateCausalKernel, indicator_of_mem huy, indicator_of_mem hu]
    have he : Complex.exp ((-z) * ((y - u : ℝ) : ℂ)) =
        Complex.exp ((-z) * (y : ℂ)) * Complex.exp (z * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  · have huy : y - u ∉ Ioi (0 : ℝ) := by
      change ¬0 < y - u
      exact not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hu))
    rw [complexRateCausalKernel, indicator_of_notMem huy, indicator_of_notMem hu,
      zero_mul, mul_zero]

/-- A zero total coefficient replaces the lower tail by the negative upper tail. -/
theorem complexCausalConvolution_eq_upper_laplace_of_zero {z : ℂ} {f : ℝ → ℂ}
    (hi : Integrable (complexLaplaceWeighted z f))
    (hz : negativeHalfLineLaplace f z = 0) (y : ℝ) :
    (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      -((Real.pi : ℂ) * Complex.exp ((-z) * (y : ℂ))) *
        ∫ u in Ioi y, Complex.exp (z * (u : ℂ)) * f u := by
  have hs := integral_add_compl (s := Iio y) measurableSet_Iio hi
  change (∫ u in Iio y, Complex.exp (z * (u : ℂ)) * f u) +
      (∫ u in (Iio y)ᶜ, Complex.exp (z * (u : ℂ)) * f u) = negativeHalfLineLaplace f z at hs
  rw [compl_Iio, hz] at hs
  have hs' : (∫ u in Iio y, Complex.exp (z * (u : ℂ)) * f u) +
      (∫ u in Ioi y, Complex.exp (z * (u : ℂ)) * f u) = 0 := by
    simpa only [restrict_Ioi_eq_restrict_Ici] using hs
  have he : (∫ u in Iio y, Complex.exp (z * (u : ℂ)) * f u) =
      -(∫ u in Ioi y, Complex.exp (z * (u : ℂ)) * f u) := by
    calc
      _ = ((∫ u in Iio y, Complex.exp (z * (u : ℂ)) * f u) +
          (∫ u in Ioi y, Complex.exp (z * (u : ℂ)) * f u)) -
          (∫ u in Ioi y, Complex.exp (z * (u : ℂ)) * f u) := by ring
      _ = _ := by rw [hs', zero_sub]
  rw [complexCausalConvolution_eq_partial_laplace, he]
  ring

/-- The reflected complex kernel integrates the upper Laplace tail. -/
theorem reflectedComplexCausalConvolution_eq_partial_laplace (z : ℂ) (y : ℝ) (f : ℝ → ℂ) :
    ((fun t => complexRateCausalKernel z (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ((Real.pi : ℂ) * Complex.exp (z * (y : ℂ))) *
        ∫ u in Ioi y, Complex.exp ((-z) * (u : ℂ)) * f u := by
  have hr : ((fun t => complexRateCausalKernel z (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ∫ u, complexRateCausalKernel z (u - y) * f u := by
    rw [convolution_def]
    have hh := integral_sub_left_eq_self (μ := volume)
      (fun u => complexRateCausalKernel z (u - y) * f u) y
    convert hh using 1
    congr 1
    funext u
    dsimp only [ContinuousLinearMap.mul_apply']
    congr 1
    congr 1
    ring
  rw [hr, ← integral_indicator measurableSet_Ioi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  by_cases hu : u ∈ Ioi y
  · have huy : u - y ∈ Ioi (0 : ℝ) := by
      change 0 < u - y
      exact sub_pos.mpr hu
    rw [complexRateCausalKernel, indicator_of_mem huy, indicator_of_mem hu]
    have he : Complex.exp ((-z) * ((u - y : ℝ) : ℂ)) =
        Complex.exp (z * (y : ℂ)) * Complex.exp ((-z) * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  · have huy : u - y ∉ Ioi (0 : ℝ) := by
      change ¬0 < u - y
      exact not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hu))
    rw [complexRateCausalKernel, indicator_of_notMem huy, indicator_of_notMem hu,
      zero_mul, mul_zero]

/-- A complex Laplace zero supplies the anti-causal resolvent representation. -/
theorem complexCausalConvolution_eq_neg_reflected_of_laplace_zero {z : ℂ} {f : ℝ → ℂ}
    (hi : Integrable (complexLaplaceWeighted z f)) (hz : negativeHalfLineLaplace f z = 0) :
    complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f =
      fun y => -(((fun t => complexRateCausalKernel (-z) (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y) := by
  funext y
  rw [complexCausalConvolution_eq_upper_laplace_of_zero hi hz y,
    reflectedComplexCausalConvolution_eq_partial_laplace]
  simp only [neg_neg, neg_mul]

end GaloisForLFunctions.HTGeometry
