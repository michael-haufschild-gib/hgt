import GaloisForLFunctions.RHTower.XiWeilDivisorHilbert
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-!
# Arithmetic evaluation of the Weil Gram off the strip

A base point below the strip has `Re (1/2 + z i) > 1`, so the logarithmic
derivative of the completed zeta there is the absolutely convergent
prime–archimedean expression

`logDeriv ξ(s) = s⁻¹ + (s−1)⁻¹ + logDeriv Γ_ℝ(s) − ∑ Λ(n) n^{−s}`.

Composing with the closure identity for the Cauchy kernel algebra writes every
Gram entry of the criterion in those terms: one absolute constant, two pole
terms, two archimedean terms and two von Mangoldt series.  The prime side enters
only through `∑ Λ(n) n^{−s}` with `Λ(n) ≥ 0`, which is the primitive the
positivity question must exploit.
-/

open Complex

namespace RHTower

noncomputable section

/-- The centered coordinate of a base point below the strip lies in the
half-plane of absolute convergence. -/
theorem one_lt_re_of_im_lt_neg_half {z : ℂ} (hz : z.im < -(1 / 2)) :
    1 < ((1 / 2 : ℂ) + z * Complex.I).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.div_re, Complex.one_re, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_apply]
  norm_num
  linarith

/-- Base points below the strip avoid the divisor. -/
theorem XiC_ne_zero_of_im_lt_neg_half {z : ℂ} (hz : z.im < -(1 / 2)) :
    XiC z ≠ 0 := by
  apply XiC_ne_zero_of_half_le_abs_im
  rw [abs_of_neg (by linarith : z.im < 0)]
  linarith

/-- **The logarithmic derivative at a base point below the strip is arithmetic.**
The centered logarithmic derivative is `I` times the prime–archimedean
expression, with the von Mangoldt series absolutely convergent. -/
theorem logDeriv_XiC_eq_arithmetic_of_im_lt_neg_half {z : ℂ}
    (hz : z.im < -(1 / 2)) :
    logDeriv XiC z =
      (((1 / 2 : ℂ) + z * Complex.I)⁻¹ +
        ((1 / 2 : ℂ) + z * Complex.I - 1)⁻¹ +
        logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + z * Complex.I) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((1 / 2 : ℂ) + z * Complex.I)) * Complex.I := by
  have hre := one_lt_re_of_im_lt_neg_half hz
  have hdf : DifferentiableAt ℂ xi ((1 / 2 : ℂ) + z * Complex.I) :=
    xi_differentiable _
  have hdg : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w * Complex.I) z := by
    fun_prop
  have hcomp := logDeriv_comp (f := xi)
    (g := fun w : ℂ => (1 / 2 : ℂ) + w * Complex.I) (x := z) hdf hdg
  have hXiC : XiC = xi ∘ (fun w : ℂ => (1 / 2 : ℂ) + w * Complex.I) := by
    funext w
    rfl
  have hd : deriv (fun w : ℂ => (1 / 2 : ℂ) + w * Complex.I) z = Complex.I := by
    simp
  rw [hXiC, hcomp, hd]
  show logDeriv xi ((1 / 2 : ℂ) + z * Complex.I) * Complex.I = _
  rw [logDeriv_xi_eq_arithmetic hre]

/-- **The Gram entry off the strip, arithmetically.**  For distinct base points
below the strip every entry of the Weil Gram is the second inverse moment
corrected by two prime–archimedean values; the only arithmetic input is the
von Mangoldt series, whose coefficients are nonnegative. -/
theorem xiWeilGramEntry_arithmetic {z z' : ℂ} (hz : z.im < -(1 / 2))
    (hz' : z'.im < -(1 / 2)) (hz0 : z ≠ 0) (hz'0 : z' ≠ 0) (hzz' : z ≠ z') :
    xiWeilGramEntry z z' =
      xiSecondInverseMoment -
        (z' / (z * (z - z'))) *
          ((((1 / 2 : ℂ) + z * Complex.I)⁻¹ +
            ((1 / 2 : ℂ) + z * Complex.I - 1)⁻¹ +
            logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + z * Complex.I) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((1 / 2 : ℂ) + z * Complex.I)) * Complex.I) +
        (z / (z' * (z - z'))) *
          ((((1 / 2 : ℂ) + z' * Complex.I)⁻¹ +
            ((1 / 2 : ℂ) + z' * Complex.I - 1)⁻¹ +
            logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + z' * Complex.I) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((1 / 2 : ℂ) + z' * Complex.I)) * Complex.I) := by
  rw [xiWeilGramEntry_eq_logDeriv (XiC_ne_zero_of_im_lt_neg_half hz)
      (XiC_ne_zero_of_im_lt_neg_half hz') hz0 hz'0 hzz',
    logDeriv_XiC_eq_arithmetic_of_im_lt_neg_half hz,
    logDeriv_XiC_eq_arithmetic_of_im_lt_neg_half hz']

/-- The prime side of a Gram entry is a series with nonnegative coefficients
tested against an explicit weight: this is the form in which `Λ(n) ≥ 0` becomes
usable. -/
theorem lseries_vonMangoldt_summable_of_im_lt_neg_half {z : ℂ}
    (hz : z.im < -(1 / 2)) :
    LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((1 / 2 : ℂ) + z * Complex.I) :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt
    (one_lt_re_of_im_lt_neg_half hz)

end

end RHTower
