import GaloisForLFunctions.SchwartzSpectralPullbackForm
import GaloisForLFunctions.RHTower.CausalFourierBridge

/-!
# Polynomial differential autocorrelation frames on Schwartz space

The normalized derivative `(2π)⁻¹ d/dx` has Fourier symbol `i t`.  Hence a polynomial
constant-coefficient differential filter has symbol `p(i t)`.  This file constructs those
filters inside Schwartz space, proves the exact multiplier law, constructs the reflected-conjugate
autocorrelation as a Schwartz function, and proves that every finite differential autocorrelation
frame has spectral density `∑ⱼ |pⱼ(i t)|²`.

The statements are generic harmonic-analysis infrastructure.  They contain no Xi function,
positivity assumption, spectral hypothesis, or Riemann-hypothesis interface.
-/

open Complex Polynomial
open scoped FourierTransform SchwartzMap Convolution ComplexConjugate

noncomputable section

namespace SchwartzMap

def momentumCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (-I) • derivCLM ℂ ℂ

def polynomialMomentum (p : Polynomial ℂ) (u : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  ∑ n ∈ p.support, p.coeff n • ((momentumCLM ^ n) u)

theorem fourier_momentumCLM (u : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier (momentumCLM u) =
      spectralMomentumCLM (FourierTransform.fourier u) := by
  exact fourier_negI_deriv_eq_spectralMomentum u

theorem fourier_momentumCLM_pow_apply
    (n : ℕ) (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier ((momentumCLM ^ n) u) t =
      (spectralMomentumMultiplier t) ^ n *
        FourierTransform.fourier u t := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih,
        fourier_momentumCLM, spectralMomentumCLM_apply]
      rw [pow_succ]
      ring

theorem fourier_polynomialMomentum_apply
    (p : Polynomial ℂ) (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier (polynomialMomentum p u) t =
      p.eval (spectralMomentumMultiplier t) *
        FourierTransform.fourier u t := by
  rw [polynomialMomentum]
  rw [FourierTransform.fourier_sum]
  simp only [FourierTransform.fourier_smul]
  rw [SchwartzMap.sum_apply]
  simp only [SchwartzMap.smul_apply]
  change (∑ x ∈ p.support,
      p.coeff x * FourierTransform.fourier ((momentumCLM ^ x) u) t) = _
  simp_rw [fourier_momentumCLM_pow_apply]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def conjugateReflection (u : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (u (-x))

theorem integrable_conjugateReflection (u : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (conjugateReflection u) := by
  simpa [conjugateReflection, Complex.conjCLE_apply] using
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp u.integrable.comp_neg)

theorem fourier_conjugateReflection (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    𝓕 (conjugateReflection u) t =
      (starRingEnd ℂ) (𝓕 (u : ℝ → ℂ) t) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_conj]
  rw [← MeasureTheory.integral_neg_eq_self]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [conjugateReflection, neg_neg, smul_eq_mul, map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

def autocorrelation (u : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  (u : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] conjugateReflection u

theorem fourier_autocorrelation (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    𝓕 (autocorrelation u) t =
      𝓕 (u : ℝ → ℂ) t * (starRingEnd ℂ) (𝓕 (u : ℝ → ℂ) t) := by
  rw [autocorrelation,
    RHTower.fourier_mul_convolution_eq_of_integrable u.integrable
      (integrable_conjugateReflection u),
    fourier_conjugateReflection]

def normalizedDerivativeCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) • derivCLM ℂ ℂ

theorem fourier_normalizedDerivativeCLM_apply
    (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier (normalizedDerivativeCLM u) t =
      ((t : ℂ) * I) * FourierTransform.fourier u t := by
  rw [normalizedDerivativeCLM, ContinuousLinearMap.smul_apply,
    FourierTransform.fourier_smul]
  have h := fourier_negI_deriv_apply u t
  rw [map_smul] at h
  change (-I) * FourierTransform.fourier (derivCLM ℂ ℂ u) t = _ at h
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  push_cast at hpi
  have hD : FourierTransform.fourier (derivCLM ℂ ℂ u) t =
      I * ((2 * Real.pi * t : ℝ) : ℂ) * FourierTransform.fourier u t := by
    apply mul_left_cancel₀ (a := -I) (by simp)
    rw [mul_assoc, h]
    rw [← mul_assoc]
    rw [show (-I) * I = (1 : ℂ) by simp]
    simp
  rw [SchwartzMap.smul_apply]
  simp only [smul_eq_mul]
  rw [hD]
  field_simp [hpi]
  push_cast
  ring

theorem fourier_normalizedDerivativeCLM_pow_apply
    (n : ℕ) (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier ((normalizedDerivativeCLM ^ n) u) t =
      ((t : ℂ) * I) ^ n * FourierTransform.fourier u t := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih,
        fourier_normalizedDerivativeCLM_apply, pow_succ]
      ring

def polynomialNormalizedDerivative
    (p : Polynomial ℂ) (u : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ n ∈ p.support, p.coeff n • ((normalizedDerivativeCLM ^ n) u)

theorem fourier_polynomialNormalizedDerivative_apply
    (p : Polynomial ℂ) (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier (polynomialNormalizedDerivative p u) t =
      p.eval ((t : ℂ) * I) * FourierTransform.fourier u t := by
  rw [polynomialNormalizedDerivative, FourierTransform.fourier_sum]
  simp only [FourierTransform.fourier_smul]
  rw [SchwartzMap.sum_apply]
  simp only [SchwartzMap.smul_apply]
  change (∑ x ∈ p.support,
      p.coeff x * FourierTransform.fourier
        ((normalizedDerivativeCLM ^ x) u) t) = _
  simp_rw [fourier_normalizedDerivativeCLM_pow_apply]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem fourier_autocorrelation_polynomialNormalizedDerivative
    (p : Polynomial ℂ) (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    𝓕 (autocorrelation (polynomialNormalizedDerivative p u)) t =
      (p.eval ((t : ℂ) * I) * (starRingEnd ℂ) (p.eval ((t : ℂ) * I))) *
      (FourierTransform.fourier u t *
          (starRingEnd ℂ) (FourierTransform.fourier u t)) := by
  rw [fourier_autocorrelation]
  have hp : 𝓕 ((polynomialNormalizedDerivative p u : SchwartzMap ℝ ℂ) : ℝ → ℂ) t =
      p.eval ((t : ℂ) * I) * FourierTransform.fourier u t := by
    exact fourier_polynomialNormalizedDerivative_apply p u t
  rw [hp]
  simp only [map_mul]
  ring

def reflectedSchwartz (u : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv) u

@[simp] theorem reflectedSchwartz_apply (u : SchwartzMap ℝ ℂ) (x : ℝ) :
    reflectedSchwartz u x = u (-x) := rfl

def conjugateReflectionSchwartz (u : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  conjSLM (reflectedSchwartz u)

@[simp] theorem conjugateReflectionSchwartz_apply
    (u : SchwartzMap ℝ ℂ) (x : ℝ) :
    conjugateReflectionSchwartz u x = (starRingEnd ℂ) (u (-x)) := by
  simp [conjugateReflectionSchwartz]

theorem fourier_conjugateReflectionSchwartz
    (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier (conjugateReflectionSchwartz u) t =
      (starRingEnd ℂ) (FourierTransform.fourier u t) := by
  rw [SchwartzMap.fourier_coe]
  change 𝓕 (conjugateReflection u) t = _
  exact fourier_conjugateReflection u t

def autocorrelationSchwartz (u : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u
    (conjugateReflectionSchwartz u)

@[simp] theorem autocorrelationSchwartz_apply
    (u : SchwartzMap ℝ ℂ) (x : ℝ) :
    autocorrelationSchwartz u x = autocorrelation u x := by
  rw [autocorrelationSchwartz, SchwartzMap.convolution_apply, autocorrelation]
  rfl

theorem fourier_autocorrelationSchwartz
    (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier (autocorrelationSchwartz u) t =
      FourierTransform.fourier u t *
        (starRingEnd ℂ) (FourierTransform.fourier u t) := by
  rw [autocorrelationSchwartz]
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f t)
    (SchwartzMap.fourier_convolution
      (ContinuousLinearMap.mul ℂ ℂ) u (conjugateReflectionSchwartz u))
  dsimp only at h
  rw [SchwartzMap.pairing_apply_apply,
    fourier_conjugateReflectionSchwartz] at h
  exact h

def finitePolynomialAutocorrelationFrame {n : ℕ}
    (p : Fin n → Polynomial ℂ) (u : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ j : Fin n,
    autocorrelationSchwartz (polynomialNormalizedDerivative (p j) u)

theorem fourier_finitePolynomialAutocorrelationFrame
    {n : ℕ} (p : Fin n → Polynomial ℂ) (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    𝓕 (finitePolynomialAutocorrelationFrame p u) t =
      (∑ j : Fin n,
        (p j).eval ((t : ℂ) * I) *
          (starRingEnd ℂ) ((p j).eval ((t : ℂ) * I))) *
        (FourierTransform.fourier u t *
          (starRingEnd ℂ) (FourierTransform.fourier u t)) := by
  rw [finitePolynomialAutocorrelationFrame,
    FourierTransform.fourier_sum]
  rw [SchwartzMap.sum_apply]
  simp_rw [fourier_autocorrelationSchwartz,
    fourier_polynomialNormalizedDerivative_apply]
  simp only [map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Cross-correlation of two Schwartz functions, with conjugate reflection in the second
argument. -/
def crossCorrelationSchwartz (u v : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u
    (conjugateReflectionSchwartz v)

theorem fourier_crossCorrelationSchwartz
    (u v : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier (crossCorrelationSchwartz u v) t =
      FourierTransform.fourier u t *
        (starRingEnd ℂ) (FourierTransform.fourier v t) := by
  rw [crossCorrelationSchwartz]
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f t)
    (SchwartzMap.fourier_convolution
      (ContinuousLinearMap.mul ℂ ℂ) u (conjugateReflectionSchwartz v))
  dsimp only at h
  rw [SchwartzMap.pairing_apply_apply,
    fourier_conjugateReflectionSchwartz] at h
  exact h

/-- First variation of autocorrelation in the direction `v`. -/
def autocorrelationTangentSchwartz (u v : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  crossCorrelationSchwartz v u + crossCorrelationSchwartz u v

theorem fourier_autocorrelationTangentSchwartz
    (u v : SchwartzMap ℝ ℂ) (t : ℝ) :
    FourierTransform.fourier (autocorrelationTangentSchwartz u v) t =
      FourierTransform.fourier v t *
          (starRingEnd ℂ) (FourierTransform.fourier u t) +
        FourierTransform.fourier u t *
          (starRingEnd ℂ) (FourierTransform.fourier v t) := by
  rw [autocorrelationTangentSchwartz, FourierTransform.fourier_add]
  simp only [SchwartzMap.add_apply]
  rw [fourier_crossCorrelationSchwartz, fourier_crossCorrelationSchwartz]

end SchwartzMap
