import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalLaplaceReflection

/-!
# Complex weighting of actual causal exponential kernels

Complex exponential weights distribute across convolution and shift the
kernel's complex rate. In the decaying half-plane, the literal weighted
kernel is integrable and its mass is exactly the resolvent coefficient.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry

/-- A complex exponential weight on a literal profile. -/
def complexLaplaceWeighted (q : ℂ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  Complex.exp (q * (u : ℂ)) * f u

/-- The normalized causal exponential at an arbitrary complex rate. -/
def complexRateCausalKernel (z : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator (fun u => (Real.pi : ℂ) * Complex.exp ((-z) * (u : ℂ)))

/-- The modulated real-rate kernel is exactly the complex-rate kernel. -/
theorem modulatedCausalExponential_eq_complexRate (a b : ℝ) :
    modulatedCausalExponential a b = complexRateCausalKernel (modulatedLaplaceRate a b) := by
  funext u
  unfold modulatedCausalExponential causalModulation _root_.RHTower.causalFourierExponential
    complexRateCausalKernel
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hu, indicator_of_mem hu]
    have he : Complex.exp (((2 * Real.pi * (-b) * u : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((Real.pi * a : ℝ) : ℂ) * (u : ℂ)) =
        Complex.exp ((-modulatedLaplaceRate a b) * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold modulatedLaplaceRate
      push_cast
      ring
    calc
      _ = (Real.pi : ℂ) *
          (Complex.exp (((2 * Real.pi * (-b) * u : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-((Real.pi * a : ℝ) : ℂ) * (u : ℂ))) := by ring
      _ = _ := by rw [he]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, mul_zero]

/-- Complex weights distribute across convolution for literal representatives. -/
theorem complexLaplaceWeighted_convolution (q : ℂ) (k f : ℝ → ℂ) :
    complexLaplaceWeighted q (k ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      complexLaplaceWeighted q k ⋆[ContinuousLinearMap.mul ℂ ℂ] complexLaplaceWeighted q f := by
  funext y
  rw [complexLaplaceWeighted, convolution_def, convolution_def, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change Complex.exp (q * (y : ℂ)) * (k t * f (y - t)) =
    complexLaplaceWeighted q k t * complexLaplaceWeighted q f (y - t)
  unfold complexLaplaceWeighted
  have he : Complex.exp (q * (y : ℂ)) =
      Complex.exp (q * (t : ℂ)) * Complex.exp (q * ((y - t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Exponential weighting subtracts the Laplace argument from the complex rate. -/
theorem complexLaplaceWeighted_causalKernel (q z : ℂ) :
    complexLaplaceWeighted q (complexRateCausalKernel z) = complexRateCausalKernel (z - q) := by
  funext u
  unfold complexLaplaceWeighted complexRateCausalKernel
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hu, indicator_of_mem hu]
    have he : Complex.exp (q * (u : ℂ)) * Complex.exp ((-z) * (u : ℂ)) =
        Complex.exp ((-(z - q)) * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      _ = (Real.pi : ℂ) * (Complex.exp (q * (u : ℂ)) * Complex.exp ((-z) * (u : ℂ))) := by ring
      _ = _ := by rw [he]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, mul_zero]

/-- Positive real part is precisely the decaying-kernel admission used here. -/
theorem integrable_complexRateCausalKernel {z : ℂ} (hz : 0 < z.re) :
    Integrable (complexRateCausalKernel z) := by
  unfold complexRateCausalKernel
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa only [Complex.neg_re] using neg_lt_zero.mpr hz) 0).const_mul
    (Real.pi : ℂ)

/-- The actual normalized complex kernel has mass π/z. -/
theorem integral_complexRateCausalKernel {z : ℂ} (hz : 0 < z.re) :
    (∫ u, complexRateCausalKernel z u) = (Real.pi : ℂ) / z := by
  unfold complexRateCausalKernel
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_mul_complex_Ioi (a := -z) (by simpa only [Complex.neg_re] using neg_lt_zero.mpr hz) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    div_eq_mul_inv, inv_neg, neg_mul_neg, one_mul]

/-- The literal convolution moment law on the side with a decaying causal kernel. -/
theorem negativeHalfLineLaplace_causalConvolution_of_lt {z q : ℂ} (hdecay : 0 < (z - q).re)
    {f : ℝ → ℂ} (hf : Integrable (complexLaplaceWeighted q f)) :
    negativeHalfLineLaplace (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) q =
      ((Real.pi : ℂ) / (z - q)) * negativeHalfLineLaplace f q := by
  change (∫ u, complexLaplaceWeighted q
      (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) u) = _
  rw [complexLaplaceWeighted_convolution, complexLaplaceWeighted_causalKernel,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_complexRateCausalKernel hdecay) hf,
    integral_complexRateCausalKernel hdecay]
  rfl

end GaloisForLFunctions.HTGeometry
