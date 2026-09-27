import GaloisForLFunctions.RHTower.XiGaussianUniformHeatHalfLine
import GaloisForLFunctions.RHTower.XiGaussianRealChannelEnergy

/-!
# Exact quadratic-factor splitting of the full Xi source and native energy

Replacing a positive real quadratic factor by its square expansion preserves
the full signed source. The native energies are not additive under this
replacement: an exact nonnegative transverse spectral moment remains.
Every theorem retains the entire cofactor polynomial and every divisor copy.
-/

open Complex Polynomial
noncomputable section
namespace RHTower

def xiGaussianLinearFactor (a : ℝ) : Polynomial ℝ := X - C a

def xiGaussianPositiveQuadratic (a b : ℝ) : Polynomial ℝ :=
  xiGaussianLinearFactor a ^ 2 + C (b ^ 2)

def xiGaussianTransverseEnergy (P : Polynomial ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  ∑' q : XiZeroCopy, (xiSpectralPoint q ^ 2).im ^ 2 *
    ‖xiPolynomialGaussianHeatTerm P t q‖

private theorem eval_linear (a : ℝ) (z : ℂ) :
    evalRealPolynomial (xiGaussianLinearFactor a) z = z - a := by
  simp [xiGaussianLinearFactor, evalRealPolynomial]

private theorem eval_quadratic (a b : ℝ) (z : ℂ) :
    evalRealPolynomial (xiGaussianPositiveQuadratic a b) z =
      (z - a) ^ 2 + (b : ℂ) ^ 2 := by
  simp [xiGaussianPositiveQuadratic, xiGaussianLinearFactor, evalRealPolynomial]

private theorem quadratic_norm_identity (z : ℂ) (b : ℝ) :
    ‖z ^ 2 + (b : ℂ) ^ 2‖ ^ 2 + 4 * b ^ 2 * z.im ^ 2 =
      ‖z‖ ^ 4 + 2 * b ^ 2 * ‖z‖ ^ 2 + b ^ 4 := by
  rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
    Complex.mul_im]
  ring

theorem summable_xiGaussianTransverseEnergy (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    Summable (fun q : XiZeroCopy => (xiSpectralPoint q ^ 2).im ^ 2 *
      ‖xiPolynomialGaussianHeatTerm P t q‖) := by
  apply Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)) _
    (summable_norm_xiPolynomialGaussianHeatTerm t.property (P * X))
  intro q
  rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm,
    evalRealPolynomial_mul, evalRealPolynomial_X, norm_mul, mul_pow]
  have hi : (xiSpectralPoint q ^ 2).im ^ 2 ≤ ‖xiSpectralPoint q ^ 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [sq_nonneg (xiSpectralPoint q ^ 2).re]
  have h := mul_le_mul_of_nonneg_right hi
    (mul_nonneg (sq_nonneg ‖evalRealPolynomial P (xiSpectralPoint q ^ 2)‖)
      (Real.exp_pos (-((t : ℝ) * (xiSpectralPoint q ^ 2).re))).le)
  nlinarith only [h]

theorem xiGaussianTransverseEnergy_nonneg (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) : 0 ≤ xiGaussianTransverseEnergy P t :=
  tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)

private theorem heat_term_split (P : Polynomial ℝ) (a b t : ℝ) (q : XiZeroCopy) :
    xiPolynomialGaussianHeatTerm (P * xiGaussianPositiveQuadratic a b) t q =
      xiPolynomialGaussianHeatTerm (P * xiGaussianLinearFactor a ^ 2) t q +
        ((2 * b ^ 2 : ℝ) : ℂ) *
          xiPolynomialGaussianHeatTerm (P * xiGaussianLinearFactor a) t q +
        ((b ^ 4 : ℝ) : ℂ) * xiPolynomialGaussianHeatTerm P t q := by
  simp only [xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul,
    evalRealPolynomial_pow, eval_linear, eval_quadratic]
  push_cast
  ring

/-- Exact signed splitting, including all cofactor coefficient cross terms. -/
theorem xiGaussianHeatTraceReal_quadratic_split (P : Polynomial ℝ)
    (a b : ℝ) (t : {t : ℝ // 0 < t}) :
    xiPolynomialGaussianHeatTraceReal (P * xiGaussianPositiveQuadratic a b) t =
      xiPolynomialGaussianHeatTraceReal (P * xiGaussianLinearFactor a ^ 2) t +
        2 * b ^ 2 * xiPolynomialGaussianHeatTraceReal (P * xiGaussianLinearFactor a) t +
        b ^ 4 * xiPolynomialGaussianHeatTraceReal P t := by
  have h₀ := summable_xiPolynomialGaussianHeatTerm t.property P
  have h₁ := summable_xiPolynomialGaussianHeatTerm t.property (P * xiGaussianLinearFactor a)
  have h₂ := summable_xiPolynomialGaussianHeatTerm t.property (P * xiGaussianLinearFactor a ^ 2)
  have h : xiPolynomialGaussianHeatTrace (P * xiGaussianPositiveQuadratic a b) t =
      xiPolynomialGaussianHeatTrace (P * xiGaussianLinearFactor a ^ 2) t +
        ((2 * b ^ 2 : ℝ) : ℂ) * xiPolynomialGaussianHeatTrace (P * xiGaussianLinearFactor a) t +
        ((b ^ 4 : ℝ) : ℂ) * xiPolynomialGaussianHeatTrace P t := by
    unfold xiPolynomialGaussianHeatTrace
    simp_rw [heat_term_split]
    rw [Summable.tsum_add (h₂.add (h₁.mul_left _)) (h₀.mul_left _),
      Summable.tsum_add h₂ (h₁.mul_left _), tsum_mul_left, tsum_mul_left]
  have hr := congrArg Complex.re h
  simpa only [xiPolynomialGaussianHeatTraceReal, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

/-- This is the full Gamma-plus-pole-minus-prime source, not an auxiliary Gram. -/
theorem xiGaussianCompletedSource_quadratic_split (P : Polynomial ℝ)
    (a b : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianCompletedSourceResidual (P * xiGaussianPositiveQuadratic a b) t =
      xiGaussianCompletedSourceResidual (P * xiGaussianLinearFactor a ^ 2) t +
        2 * b ^ 2 * xiGaussianCompletedSourceResidual (P * xiGaussianLinearFactor a) t +
        b ^ 4 * xiGaussianCompletedSourceResidual P t := by
  simp only [xiGaussianCompletedSourceResidual_eq_trace,
    xiGaussianHeatTraceReal_quadratic_split]
  ring

private theorem native_atom_split (P : Polynomial ℝ) (a b t : ℝ) (q : XiZeroCopy) :
    ‖xiPolynomialGaussianHeatTerm (P * xiGaussianPositiveQuadratic a b) t q‖ +
      4 * b ^ 2 * ((xiSpectralPoint q ^ 2).im ^ 2 * ‖xiPolynomialGaussianHeatTerm P t q‖) =
      ‖xiPolynomialGaussianHeatTerm (P * xiGaussianLinearFactor a ^ 2) t q‖ +
        2 * b ^ 2 * ‖xiPolynomialGaussianHeatTerm (P * xiGaussianLinearFactor a) t q‖ +
        b ^ 4 * ‖xiPolynomialGaussianHeatTerm P t q‖ := by
  have h := quadratic_norm_identity (xiSpectralPoint q ^ 2 - a) b
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
  simp only [norm_xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul,
    evalRealPolynomial_pow, eval_linear, eval_quadratic, norm_mul, norm_pow, mul_pow]
  linear_combination (‖evalRealPolynomial P (xiSpectralPoint q ^ 2)‖ ^ 2 *
    Real.exp (-(t * (xiSpectralPoint q ^ 2).re))) * h

/-- The branch native energy has an exact transverse surplus. -/
theorem xiGaussianNativeEnergy_quadratic_split (P : Polynomial ℝ)
    (a b : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianNativeEnergy (P * xiGaussianPositiveQuadratic a b) t +
      4 * b ^ 2 * xiGaussianTransverseEnergy P t =
      xiGaussianNativeEnergy (P * xiGaussianLinearFactor a ^ 2) t +
        2 * b ^ 2 * xiGaussianNativeEnergy (P * xiGaussianLinearFactor a) t +
        b ^ 4 * xiGaussianNativeEnergy P t := by
  have h₀ := summable_norm_xiPolynomialGaussianHeatTerm t.property P
  have h₁ := summable_norm_xiPolynomialGaussianHeatTerm t.property (P * xiGaussianLinearFactor a)
  have h₂ := summable_norm_xiPolynomialGaussianHeatTerm t.property (P * xiGaussianLinearFactor a ^ 2)
  have hf := summable_norm_xiPolynomialGaussianHeatTerm t.property (P * xiGaussianPositiveQuadratic a b)
  have hT := summable_xiGaussianTransverseEnergy P t
  have h : (∑' q : XiZeroCopy,
      (‖xiPolynomialGaussianHeatTerm (P * xiGaussianPositiveQuadratic a b) t q‖ +
        4 * b ^ 2 * ((xiSpectralPoint q ^ 2).im ^ 2 * ‖xiPolynomialGaussianHeatTerm P t q‖))) =
      ∑' q : XiZeroCopy,
        (‖xiPolynomialGaussianHeatTerm (P * xiGaussianLinearFactor a ^ 2) t q‖ +
          2 * b ^ 2 * ‖xiPolynomialGaussianHeatTerm (P * xiGaussianLinearFactor a) t q‖ +
          b ^ 4 * ‖xiPolynomialGaussianHeatTerm P t q‖) :=
    tsum_congr (native_atom_split P a b (t : ℝ))
  rw [Summable.tsum_add hf (hT.mul_left _),
    Summable.tsum_add (h₂.add (h₁.mul_left _)) (h₀.mul_left _),
    Summable.tsum_add h₂ (h₁.mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left] at h
  exact h

/-- Half of the surplus is lost when branch real-channel energies are combined. -/
theorem xiGaussianRealChannel_quadratic_split (P : Polynomial ℝ)
    (a b : ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianRealChannelEnergy (P * xiGaussianPositiveQuadratic a b) t +
      2 * b ^ 2 * xiGaussianTransverseEnergy P t =
      xiGaussianRealChannelEnergy (P * xiGaussianLinearFactor a ^ 2) t +
        2 * b ^ 2 * xiGaussianRealChannelEnergy (P * xiGaussianLinearFactor a) t +
        b ^ 4 * xiGaussianRealChannelEnergy P t := by
  have hK := xiGaussianNativeEnergy_quadratic_split P a b t
  have hH := xiGaussianHeatTraceReal_quadratic_split P a b t
  simp only [xiGaussianRealChannelEnergy_eq_half_energy_add_trace]
  change (xiGaussianNativeEnergy (P * xiGaussianPositiveQuadratic a b) t + _) / 2 + _ =
    (xiGaussianNativeEnergy (P * xiGaussianLinearFactor a ^ 2) t + _) / 2 +
      2 * b ^ 2 * ((xiGaussianNativeEnergy (P * xiGaussianLinearFactor a) t + _) / 2) +
      b ^ 4 * ((xiGaussianNativeEnergy P t + _) / 2)
  nlinarith only [hK, hH]

end RHTower
