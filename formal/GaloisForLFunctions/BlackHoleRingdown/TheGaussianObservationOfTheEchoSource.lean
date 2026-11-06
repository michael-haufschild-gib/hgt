import GaloisForLFunctions.BlackHoleRingdown.TheEchoSpikesAndTheirGaussianObservation
import GaloisForLFunctions.BlackHoleRingdown.TheProbesPreserveEveryResonance
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Convolution

/-!
# The Gaussian observation has the arithmetic source transform

Exponential weighting turns the Gaussian observation of the totient echo train into a
convolution of two integrable functions. Its Laplace transform is therefore the original
completed-zeta quotient times the Gaussian multiplier. This connects the smoothed time signal
to the arithmetic source without replacing the source by a prescribed divisor.

Gaussian observation of an exponential mode is evaluated exactly, so subtracting the mean in
the source gives the same mean-subtracted observation.
-/

open Complex MeasureTheory Filter Topology
open scoped Convolution
noncomputable section
namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower

/-- Exact Gaussian observation of an exponential mode. -/
theorem integral_gaussian_mul_exponential {σ : ℝ} (hσ : 0 < σ) (b t : ℝ) :
    (∫ u : ℝ, Real.exp (-σ * (t - u) ^ 2) * Real.exp (b * u)) =
      Real.sqrt (Real.pi / σ) * Real.exp (b * t + b ^ 2 / (4 * σ)) := by
  have he (u : ℝ) : Real.exp (-σ * (t - u) ^ 2) * Real.exp (b * u) =
      Real.exp (-σ * (u - (t + b / (2 * σ))) ^ 2) *
        Real.exp (b * t + b ^ 2 / (4 * σ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp [hσ.ne']
    <;> ring
  simp_rw [he]
  rw [integral_mul_const,
    integral_sub_right_eq_self (fun u : ℝ => Real.exp (-σ * u ^ 2)) (t + b / (2 * σ)),
    integral_gaussian]

theorem integrable_gaussian_mul_exponential {σ : ℝ} (hσ : 0 < σ) (b t : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-σ * (t - u) ^ 2) * Real.exp (b * u)) := by
  by_contra hi
  have h := integral_gaussian_mul_exponential hσ b t
  rw [integral_undef hi] at h
  have hp : 0 < Real.sqrt (Real.pi / σ) * Real.exp (b * t + b ^ 2 / (4 * σ)) := by
    positivity
  linarith

/-- Subtraction of the exponential mean occurs on the original source before observation. -/
theorem gaussianEcho_sub_mean {σ : ℝ} (hσ : 0 < σ) (A b t : ℝ) :
    gaussianEcho σ t - A * Real.sqrt (Real.pi / σ) *
        Real.exp (b * t + b ^ 2 / (4 * σ)) =
      ∫ u : ℝ, Real.exp (-σ * (t - u) ^ 2) *
        (echoKernel u - A * Real.exp (b * u)) := by
  have he (u : ℝ) : Real.exp (-σ * (t - u) ^ 2) *
      (echoKernel u - A * Real.exp (b * u)) =
      Real.exp (-σ * (t - u) ^ 2) * echoKernel u -
        A * (Real.exp (-σ * (t - u) ^ 2) * Real.exp (b * u)) := by ring
  simp_rw [he]
  rw [integral_sub (integrable_gaussian_mul_echoKernel hσ t)
    ((integrable_gaussian_mul_exponential hσ b t).const_mul A), integral_const_mul,
    integral_gaussian_mul_exponential hσ b t, gaussianEcho]
  ring

/-- The bilateral Laplace multiplier of a Gaussian pulse. -/
def gaussianLaplaceFactor (σ : ℝ) (w : ℂ) : ℂ :=
  ((Real.pi : ℂ) / σ) ^ (1 / 2 : ℂ) * Complex.exp (w ^ 2 / (4 * σ))

private theorem integrable_weighted_gaussian {σ : ℝ} (hσ : 0 < σ) (w : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-w * t) * Complex.exp (-(σ : ℂ) * (t : ℂ) ^ 2)) := by
  have h := integrable_cexp_quadratic (b := (σ : ℂ)) hσ (-w) 0
  simpa only [add_zero, Complex.exp_add, mul_comm] using h

theorem integral_weighted_gaussian {σ : ℝ} (hσ : 0 < σ) (w : ℂ) :
    (∫ t : ℝ, Complex.exp (-w * t) * Complex.exp (-(σ : ℂ) * (t : ℂ) ^ 2)) =
      gaussianLaplaceFactor σ w := by
  simp_rw [← Complex.exp_add, add_comm (-w * _)]
  have h := integral_cexp_quadratic (b := -(σ : ℂ))
    (by simpa only [neg_re, ofReal_re] using neg_lt_zero.mpr hσ) (-w) 0
  simp only [add_zero, neg_neg, zero_sub, neg_sq, mul_neg, div_neg] at h
  exact h

/-- Exponential weighting commutes with observation as a genuine integrable convolution. -/
theorem weighted_gaussianEcho_eq_convolution (σ : ℝ) (w : ℂ) (t : ℝ) :
    Complex.exp (-w * t) * (gaussianEcho σ t : ℂ) =
      ((fun u : ℝ => Complex.exp (-w * u) * (echoKernel u : ℂ)) ⋆[
          ContinuousLinearMap.mul ℂ ℂ]
        (fun u : ℝ => Complex.exp (-w * u) *
          Complex.exp (-(σ : ℂ) * (u : ℂ) ^ 2))) t := by
  rw [gaussianEcho, ← integral_complex_ofReal, ← integral_const_mul, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [ContinuousLinearMap.mul_apply', Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_sub]
  have he : Complex.exp (-w * (t : ℂ)) =
      Complex.exp (-w * (u : ℂ)) * Complex.exp (-w * ((t : ℂ) - u)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- The observed source has an absolutely convergent transform throughout the original half-plane. -/
theorem integrable_weighted_gaussianEcho {σ : ℝ} (hσ : 0 < σ) {w : ℂ}
    (hw : 1 / 2 < w.re) :
    Integrable (fun t : ℝ => Complex.exp (-w * t) * (gaussianEcho σ t : ℂ)) := by
  simp_rw [weighted_gaussianEcho_eq_convolution]
  exact (integrable_cexp_mul_echoKernel hw).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_weighted_gaussian hσ w)

/-- The observation is tied to the actual totient source by its exact Laplace transform. -/
theorem laplace_gaussianEcho {σ : ℝ} (hσ : 0 < σ) {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ t : ℝ, Complex.exp (-w * t) * (gaussianEcho σ t : ℂ)) =
      gaussianLaplaceFactor σ w * (completedRiemannZeta (2 * w) /
        completedRiemannZeta (2 * w + 1)) := by
  simp_rw [weighted_gaussianEcho_eq_convolution]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_cexp_mul_echoKernel hw) (integrable_weighted_gaussian hσ w),
    ContinuousLinearMap.mul_apply', integral_cexp_mul_echoKernel_eq_completed hw,
    integral_weighted_gaussian hσ w, mul_comm]

/-- Meromorphic continuation of the observed source transform, retaining the mean's kinematic pole. -/
def gaussianEchoSymbol (σ : ℝ) (ω : ℂ) : ℂ :=
  ((Real.pi : ℂ) / σ) ^ (1 / 2 : ℂ) *
    ((1 / 2 - I * ω) / (1 / 2 - I * ω - 1)) *
      gaussianResponse (1 / (4 * σ)) 0 ω

/-- The literal observed echo source reads the same Gaussian-probed causal symbol, including
the elementary kinematic factor removed by normalization. -/
theorem fourierLaplaceTransform_gaussianEcho {σ : ℝ} (hσ : 0 < σ) {ω : ℂ}
    (hω : 1 / 2 < ω.im) :
    (∫ t : ℝ, Complex.exp (I * ω * t) * (gaussianEcho σ t : ℂ)) =
      gaussianEchoSymbol σ ω := by
  have hw : 1 / 2 < (-I * ω).re := by simpa using hω
  have hk : Integrable (fun t : ℝ => Complex.exp (I * ω * t) * (echoKernel t : ℂ)) := by
    simpa only [neg_mul, neg_neg] using integrable_cexp_mul_echoKernel (w := -I * ω) hw
  have hg : Integrable (fun t : ℝ => Complex.exp (I * ω * t) *
      Complex.exp (-(σ : ℂ) * (t : ℂ) ^ 2)) := by
    simpa only [neg_mul, neg_neg] using integrable_weighted_gaussian hσ (-I * ω)
  have he (t : ℝ) : Complex.exp (I * ω * t) * (gaussianEcho σ t : ℂ) =
      ((fun u : ℝ => Complex.exp (I * ω * u) * (echoKernel u : ℂ)) ⋆[
          ContinuousLinearMap.mul ℂ ℂ]
        (fun u : ℝ => Complex.exp (I * ω * u) *
          Complex.exp (-(σ : ℂ) * (u : ℂ) ^ 2))) t := by
    simpa only [neg_mul, neg_neg] using weighted_gaussianEcho_eq_convolution σ (-I * ω) t
  have hK : (∫ t : ℝ, Complex.exp (I * ω * t) * (echoKernel t : ℂ)) =
      ((1 / 2 - I * ω) / (1 / 2 - I * ω - 1)) * causalSymbol 0 ω := by
    simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul, ofReal_zero, zero_add] using
      retardedTransform_dampedEchoKernel (D := 0) (ω := ω) (by simpa using hω)
  simp_rw [he]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hk hg,
    ContinuousLinearMap.mul_apply', hK, gaussianPulse_transform hσ ω,
    gaussianEchoSymbol, gaussianResponse]
  ring

/-- The literal source observation retains every Xi pole with its exact multiplicity. -/
theorem gaussianEchoSymbol_resonance_order {σ : ℝ} (hσ : 0 < σ) (q : XiZeroCopy) :
    meromorphicOrderAt (gaussianEchoSymbol σ) (resonanceFrequency 0 (xiSpectralPoint q)) =
      -meromorphicOrderAt XiC (xiSpectralPoint q) := by
  let ω := resonanceFrequency 0 (xiSpectralPoint q)
  have hr := ringdownRate_mem_open_strip 0 q
  have hre : (1 / 2 - I * ω).re = 1 / 2 + ω.im := by simp
  have hslo : 0 < (1 / 2 - I * ω).re := by
    rw [hre]
    dsimp [ω]
    rw [resonanceFrequency_im]
    linarith [hr.2]
  have hshi : (1 / 2 - I * ω).re < 1 / 2 := by
    rw [hre]
    dsimp [ω]
    rw [resonanceFrequency_im]
    linarith [hr.1]
  have hn : (1 / 2 - I * ω : ℂ) ≠ 0 := by
    intro h
    rw [h] at hslo
    norm_num at hslo
  have hd : (1 / 2 - I * ω - 1 : ℂ) ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at hshi
    norm_num at hshi
  have hm : ((Real.pi : ℂ) / σ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero
      (ofReal_ne_zero.mpr Real.pi_ne_zero) (ofReal_ne_zero.mpr hσ.ne')))
  have hs : AnalyticAt ℂ (fun z : ℂ => 1 / 2 - I * z) ω := by fun_prop
  have hg : AnalyticAt ℂ (fun z : ℂ => ((Real.pi : ℂ) / σ) ^ (1 / 2 : ℂ) *
      ((1 / 2 - I * z) / (1 / 2 - I * z - 1))) ω :=
    analyticAt_const.mul (hs.div (hs.sub analyticAt_const) hd)
  change meromorphicOrderAt
    ((fun z : ℂ => ((Real.pi : ℂ) / σ) ^ (1 / 2 : ℂ) *
      ((1 / 2 - I * z) / (1 / 2 - I * z - 1))) * gaussianResponse (1 / (4 * σ)) 0) ω = _
  rw [meromorphicOrderAt_mul_of_ne_zero hg (mul_ne_zero hm (div_ne_zero hn hd)),
    gaussianResponse_meromorphicOrderAt]
  exact causalSymbol_resonance_order 0 q

theorem gaussianEchoSymbol_resonance_isPole {σ : ℝ} (hσ : 0 < σ) (q : XiZeroCopy) :
    meromorphicOrderAt (gaussianEchoSymbol σ) (resonanceFrequency 0 (xiSpectralPoint q)) < 0 := by
  rw [gaussianEchoSymbol_resonance_order hσ, ← causalSymbol_resonance_order 0 q]
  exact causalSymbol_resonance_isPole 0 q

#print axioms gaussianEcho_sub_mean
#print axioms integrable_weighted_gaussianEcho
#print axioms laplace_gaussianEcho
#print axioms fourierLaplaceTransform_gaussianEcho
#print axioms gaussianEchoSymbol_resonance_order
#print axioms gaussianEchoSymbol_resonance_isPole

end GaloisForLFunctions.BlackHoleRingdown
