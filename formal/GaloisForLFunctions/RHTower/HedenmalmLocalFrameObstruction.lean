import GaloisForLFunctions.SchwartzPolynomialDifferentialFrame
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace
import GaloisForLFunctions.RHTower.XiFiniteLocalSpectralFrameObstruction
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality

/-!
# The Hedenmalm horizontal current has no finite local autocorrelation frame

For `0 < a < 1`, the exponentially tilted theta-cusp source is a concrete Schwartz function whose
Fourier transform is the completed Xi function on the vertical line `re s = 1/2 + a`.  Multiplying
the source by `-x` gives its horizontal tangent.  The first variation of its autocorrelation has
Fourier transform equal to the horizontal derivative of the Xi modulus square.

This module proves that the resulting Schwartz function cannot be a finite sum of autocorrelations
of constant-coefficient polynomial differential filters applied to the same source.  Such an
identity would produce a polynomial Hermitian-diagonal multiplier law; the completed logarithmic
flux would then propagate every Xi zero by a positive real shift, contradicting the critical-strip
location of the Xi divisor.

The obstruction is therefore stated directly in source space.  There is no abstract sign,
factorization, or reconstruction hypothesis in the final theorem.
-/

open Complex Polynomial MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap Convolution ComplexConjugate

noncomputable section
namespace RHTower

def thetaCuspRightLineSource (a : ℝ) (ha : |a| < 1) : SchwartzMap ℝ ℂ :=
  thetaCuspTiltedSchwartz (-a) (by simpa using ha)

@[simp] theorem thetaCuspRightLineSource_apply
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    thetaCuspRightLineSource a ha x =
      (Real.exp (-a * x) * thetaCuspFullSource x : ℝ) := by
  rw [thetaCuspRightLineSource, thetaCuspTiltedSchwartz_apply]

theorem fourier_thetaCuspRightLineSource_scaled
    {a : ℝ} (ha : |a| < 1) (b : ℝ) :
    FourierTransform.fourier (thetaCuspRightLineSource a ha)
        (b / (2 * Real.pi)) =
      xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) := by
  rw [thetaCuspRightLineSource,
    fourier_thetaCuspTiltedSchwartz_scaled]
  rw [XiC]
  congr 1
  push_cast
  rw [show (-a : ℂ) = -(a : ℂ) by norm_cast]
  simp [add_mul, mul_assoc, I_mul_I]
  ring

def thetaCuspRightLineTangent (a : ℝ) (ha : |a| < 1) : SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => -x))
    (thetaCuspRightLineSource a ha)

@[simp] theorem thetaCuspRightLineTangent_apply
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    thetaCuspRightLineTangent a ha x =
      (-x) * thetaCuspRightLineSource a ha x := by
  rw [thetaCuspRightLineTangent]
  have hg : Function.HasTemperateGrowth (fun x : ℝ => -x) :=
    Function.HasTemperateGrowth.id'.neg
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simp [smul_eq_mul]

theorem deriv_thetaCuspFourierLaplace_eq_integral
    {w : ℂ} (hw : |w.im| < 1) :
    deriv thetaCuspFourierLaplace w =
      ∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand w x := by
  exact (hasDerivAt_thetaCuspFourierLaplace hw).deriv

theorem deriv_thetaCuspFourierLaplace_eq_deriv_XiC
    {w : ℂ} (hw : w ∈ thetaCuspFourierLaplaceStrip) :
    deriv thetaCuspFourierLaplace w = deriv XiC w := by
  have heq : thetaCuspFourierLaplace =ᶠ[𝓝 w] XiC :=
    thetaCuspFourierLaplace_eq_XiC_on_strip.eventuallyEq_of_mem
      (isOpen_thetaCuspFourierLaplaceStrip.mem_nhds hw)
  exact heq.deriv_eq

theorem deriv_XiC_eq_deriv_xi_mul_I (w : ℂ) :
    deriv XiC w = deriv xi ((1 : ℂ) / 2 + w * I) * I := by
  have hinner : HasDerivAt (fun z : ℂ => (1 : ℂ) / 2 + z * I) I w := by
    convert ((hasDerivAt_id w).mul_const I).const_add ((1 : ℂ) / 2) using 1 <;> ring
  have hxi : HasDerivAt xi (deriv xi ((1 : ℂ) / 2 + w * I))
      ((1 : ℂ) / 2 + w * I) :=
    (xi_analyticOnNhd_univ _ (Set.mem_univ _)).differentiableAt.hasDerivAt
  simpa only [XiC] using (hxi.comp w hinner).deriv

theorem fourier_thetaCuspRightLineTangent_scaled
    {a : ℝ} (ha : |a| < 1) (b : ℝ) :
    FourierTransform.fourier (thetaCuspRightLineTangent a ha)
        (b / (2 * Real.pi)) =
      deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) := by
  rw [SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul]
  let w : ℂ := (b : ℂ) - (a : ℂ) * I
  have hw : |w.im| < 1 := by
    dsimp [w]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, zero_mul, sub_self, zero_add]
    simpa using ha
  have hwmem : w ∈ thetaCuspFourierLaplaceStrip := abs_lt.mp hw
  have hint :
      (∫ x : ℝ,
        Complex.exp (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I) •
          thetaCuspRightLineTangent a ha x) =
        -I * (∫ x : ℝ,
          thetaCuspFourierLaplaceDerivativeIntegrand w x) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [thetaCuspRightLineTangent_apply, thetaCuspRightLineSource_apply]
    simp only [smul_eq_mul, thetaCuspFourierLaplaceDerivativeIntegrand,
      thetaCuspFourierLaplaceIntegrand]
    rw [show ((Real.exp (-a * x) * thetaCuspFullSource x : ℝ) : ℂ) =
        (Real.exp (-a * x) : ℂ) * (thetaCuspFullSource x : ℂ) by norm_cast,
      Complex.ofReal_exp]
    dsimp [w]
    have hexp :
        Complex.exp (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I) *
            Complex.exp ((-a * x : ℝ) : ℂ) =
          Complex.exp (-I * ((b : ℂ) - (a : ℂ) * I) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
      simp [mul_sub, mul_assoc, ← mul_assoc, I_mul_I]
      rw [mul_assoc (x : ℂ) I I, I_mul_I]
      ring
    calc
      Complex.exp (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I) *
            (-(x : ℂ) * (Complex.exp ((-a * x : ℝ) : ℂ) *
              (thetaCuspFullSource x : ℂ))) =
          (Complex.exp (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I) *
            Complex.exp ((-a * x : ℝ) : ℂ)) *
              (-(x : ℂ) * (thetaCuspFullSource x : ℂ)) := by ring
      _ = Complex.exp (-I * ((b : ℂ) - (a : ℂ) * I) * (x : ℂ)) *
              (-(x : ℂ) * (thetaCuspFullSource x : ℂ)) := by rw [hexp]
      _ = -I * (-I * (x : ℂ) *
            (Complex.exp (-I * ((b : ℂ) - (a : ℂ) * I) * (x : ℂ)) *
              (thetaCuspFullSource x : ℂ))) := by
        ring_nf
        rw [I_sq]
        ring
  rw [hint, ← deriv_thetaCuspFourierLaplace_eq_integral hw,
    deriv_thetaCuspFourierLaplace_eq_deriv_XiC hwmem,
    deriv_XiC_eq_deriv_xi_mul_I]
  have harg : (1 : ℂ) / 2 + w * I =
      (1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I := by
    dsimp [w]
    simp [sub_mul, mul_assoc, I_mul_I]
    ring
  rw [harg]
  calc
    -I * (deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) * I) =
        ((-I) * I) *
          deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) := by ring
    _ = deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) := by simp

def thetaCuspHorizontalAutocorrelationTangent
    (a : ℝ) (ha : |a| < 1) : SchwartzMap ℝ ℂ :=
  SchwartzMap.autocorrelationTangentSchwartz
    (thetaCuspRightLineSource a ha) (thetaCuspRightLineTangent a ha)

theorem fourier_thetaCuspHorizontalAutocorrelationTangent_scaled
    {a : ℝ} (ha : |a| < 1) (b : ℝ) :
    FourierTransform.fourier
        (thetaCuspHorizontalAutocorrelationTangent a ha)
        (b / (2 * Real.pi)) =
      deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
          xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) +
        xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
          deriv xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) := by
  rw [thetaCuspHorizontalAutocorrelationTangent,
    SchwartzMap.fourier_autocorrelationTangentSchwartz,
    fourier_thetaCuspRightLineTangent_scaled,
    fourier_thetaCuspRightLineSource_scaled]
  rw [← xi_conj, ← xi_deriv_conj]
  have harg : (starRingEnd ℂ)
      ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) =
        (1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I := by
    have hhalf : (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    rw [map_add, map_add, map_mul, hhalf]
    simp
    ring
  rw [harg]

def rescaleDifferentialPolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p.comp (Polynomial.C (((2 * Real.pi : ℝ) : ℂ)⁻¹) * Polynomial.X)

theorem rescaleDifferentialPolynomial_eval_ib
    (p : Polynomial ℂ) (b : ℝ) :
    (rescaleDifferentialPolynomial p).eval ((b : ℂ) * I) =
      p.eval (((b / (2 * Real.pi) : ℝ) : ℂ) * I) := by
  rw [rescaleDifferentialPolynomial, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem xiFiniteLocalPolynomialSpectralFrame_of_spatial_identity
    {a : ℝ} (ha : |a| < 1) {n : ℕ} (p : Fin n → Polynomial ℂ)
    (hframe : thetaCuspHorizontalAutocorrelationTangent a ha =
      SchwartzMap.finitePolynomialAutocorrelationFrame p
        (thetaCuspRightLineSource a ha)) :
    XiFiniteLocalPolynomialSpectralFrame a := by
  refine ⟨n, fun j => rescaleDifferentialPolynomial (p j), ?_⟩
  intro b
  have hFourier := congrArg
    (fun u : SchwartzMap ℝ ℂ =>
      FourierTransform.fourier u (b / (2 * Real.pi))) hframe
  change FourierTransform.fourier
      (thetaCuspHorizontalAutocorrelationTangent a ha)
        (b / (2 * Real.pi)) =
    FourierTransform.fourier
      (SchwartzMap.finitePolynomialAutocorrelationFrame p
        (thetaCuspRightLineSource a ha)) (b / (2 * Real.pi)) at hFourier
  rw [fourier_thetaCuspHorizontalAutocorrelationTangent_scaled,
    SchwartzMap.fourier_finitePolynomialAutocorrelationFrame,
    fourier_thetaCuspRightLineSource_scaled] at hFourier
  rw [Polynomial.eval_finsetSum]
  simp_rw [polynomialSpectralSquare_eval_real,
    rescaleDifferentialPolynomial_eval_ib]
  have hconj : (starRingEnd ℂ)
      (xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I)) =
        xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) := by
    rw [← xi_conj]
    congr 1
    have hhalf : (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    rw [map_add, map_add, map_mul, hhalf]
    simp
    ring
  rw [hconj] at hFourier
  simpa only [mul_assoc] using hFourier

theorem no_finitePolynomialAutocorrelationFrame_for_Hedenmalm_tangent
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ¬ ∃ (n : ℕ) (p : Fin n → Polynomial ℂ),
      thetaCuspHorizontalAutocorrelationTangent a (by rw [abs_of_pos ha]; exact ha1) =
        SchwartzMap.finitePolynomialAutocorrelationFrame p
          (thetaCuspRightLineSource a (by rw [abs_of_pos ha]; exact ha1)) := by
  rintro ⟨n, p, hframe⟩
  let hstrip : |a| < 1 := by rw [abs_of_pos ha]; exact ha1
  have hlocal := xiFiniteLocalPolynomialSpectralFrame_of_spatial_identity
    hstrip p (by simpa only [hstrip] using hframe)
  exact not_XiFiniteLocalPolynomialSpectralFrame_of_pos ha hlocal

end RHTower
