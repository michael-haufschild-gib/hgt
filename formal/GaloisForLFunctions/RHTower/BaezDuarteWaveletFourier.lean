import GaloisForLFunctions.RHTower.BaezDuarteWaveletLaplace
import GaloisForLFunctions.RHTower.BaezDuarteWaveletPairing
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

/-!
# The Fourier transform of the beta wavelet

The wavelet is causal, bounded by `(2k+4)e^{-t}`, and therefore lies in `L¹ ∩ L²`.  Its classical
Fourier integral is the causal Laplace transform evaluated on the imaginary axis, which the beta
substitution already computed.
-/

namespace RHTower

open Real MeasureTheory FourierTransform

noncomputable section

theorem integrable_bdKernelVector (k : ℕ) : Integrable (bdKernelVector k) := by
  refine Integrable.mono ((integrable_causalPoleVector).const_mul (((2 * (k : ℝ) + 4) : ℝ) : ℂ))
    (measurable_bdKernelVector k).aestronglyMeasurable ?_
  filter_upwards with t
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · rw [bdKernelVector, Set.indicator_of_mem ht, causalPoleVector, Set.indicator_of_mem ht]
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_exp]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ) + 4)]
    simpa using norm_bdKernel_le k ht
  · rw [bdKernelVector, Set.indicator_of_notMem ht, norm_zero]
    positivity

theorem fourierIntegral_bdKernelVector (k : ℕ) (ξ : ℝ) :
    𝓕 (bdKernelVector k) ξ
      = (1 / 2) * (Complex.betaIntegral ((1 + 2 * Real.pi * Complex.I * (ξ : ℂ)) / 2) ((k : ℂ) + 1)
          - (2 * (k : ℂ) + 3)
            * Complex.betaIntegral ((1 + 2 * Real.pi * Complex.I * (ξ : ℂ)) / 2 + 1)
                ((k : ℂ) + 1)) := by
  set z : ℂ := 2 * Real.pi * Complex.I * (ξ : ℂ) with hz
  have hzre : -1 < z.re := by
    rw [hz]
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [← laplace_bdKernel k hzre, Real.fourier_real_eq]
  have hfun : (fun v : ℝ => (Real.fourierChar (-(v * ξ))) • bdKernelVector k v)
      = Set.indicator (Set.Ioi (0 : ℝ))
          (fun t : ℝ => ((bdKernel k t : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ)))) := by
    funext v
    by_cases hv : v ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hv, bdKernelVector, Set.indicator_of_mem hv]
      show ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) * ((bdKernel k v : ℝ) : ℂ)
        = ((bdKernel k v : ℝ) : ℂ) * Complex.exp (-(z * (v : ℂ)))
      rw [Real.fourierChar_apply, mul_comm]
      congr 2
      rw [hz]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hv, bdKernelVector, Set.indicator_of_notMem hv, smul_zero]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi]

end

end RHTower
