import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZetaPoles
import GaloisForLFunctions.HTGeometry.HardyTaylorCoefficient
import GaloisForLFunctions.HTGeometry.AffineFluxTaylorCoeff

/-!
# Analytic continuation of the arithmetic zeta quotient series

The Taylor series of the rational zeta function equals the formal series determined
by all extension point counts. Taylor multiplicativity and linear rescaling then
identify the shifted quotient with its convergent series at zero. Thus its proved
meromorphic poles belong to the continuation of that same arithmetic series.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

private def denominatorPolynomial : ℂ[X] := (1 - X) * (1 - C 3 * X)

private lemma denominatorPolynomial_eval (T : ℂ) :
    denominatorPolynomial.eval T = (1 - T) * (1 - 3 * T) := by
  simp only [denominatorPolynomial, eval_mul, eval_sub, eval_one, eval_X, eval_C]

private lemma denominatorPolynomial_coe :
    (denominatorPolynomial : PowerSeries ℂ) =
      (1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X) := by
  simp only [denominatorPolynomial, coe_mul, coe_sub, coe_one, coe_X, coe_C]

private lemma denominatorPolynomial_ne_zero : (denominatorPolynomial : PowerSeries ℂ) ≠ 0 := by
  intro h
  have hc := congrArg PowerSeries.constantCoeff h
  simp [denominatorPolynomial_coe] at hc

private lemma taylorPS_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 (0 : ℂ)] g) :
    taylorPS f = taylorPS g := by
  ext n
  rw [coeff_taylorPS, coeff_taylorPS, h.iteratedDeriv_eq n]

lemma zetaFunction_zero : zetaFunction 0 = 1 := by
  simp only [zetaFunction, mul_zero, sub_zero, one_mul, div_one,
    ← Polynomial.coeff_zero_eq_eval_zero]
  exact numerator_constantCoeff

lemma zetaFunction_analytic_zero : AnalyticAt ℂ zetaFunction 0 :=
  zetaFunction_analytic 0 (by norm_num)

/-- The analytic Taylor series is the series fixed by the actual point counts. -/
theorem zetaFunction_taylor : taylorPS zetaFunction = zeta := by
  have hD : AnalyticAt ℂ (fun T => denominatorPolynomial.eval T) 0 := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun T : ℂ => T) 0).aeval_polynomial
      denominatorPolynomial
  have hD0 : denominatorPolynomial.eval 0 ≠ 0 := by
    rw [denominatorPolynomial_eval]
    norm_num
  have he : (fun T => denominatorPolynomial.eval T * zetaFunction T) =ᶠ[𝓝 (0 : ℂ)]
      (fun T => numerator.eval T) := by
    filter_upwards [hD.continuousAt.eventually_ne hD0] with T hT
    rw [denominatorPolynomial_eval] at hT ⊢
    unfold zetaFunction
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hT
  have ht : (denominatorPolynomial : PowerSeries ℂ) * taylorPS zetaFunction =
      (numerator : PowerSeries ℂ) := by
    rw [← HTGeometry.taylorPS_polynomial_eval_hardy denominatorPolynomial,
      ← HTGeometry.taylorPS_mul_of_analyticAt_hardy hD zetaFunction_analytic_zero]
    change taylorPS (fun T => denominatorPolynomial.eval T * zetaFunction T) = _
    rw [taylorPS_congr he, HTGeometry.taylorPS_polynomial_eval_hardy]
  apply mul_left_cancel₀ denominatorPolynomial_ne_zero
  rw [ht, denominatorPolynomial_coe, zeta_rational]

private lemma taylorPS_divide_three (f : ℂ → ℂ) :
    taylorPS (fun T : ℂ => f (T / 3)) = PowerSeries.rescale (1 / 3 : ℂ) (taylorPS f) := by
  have he : (fun T : ℂ => f (T / 3)) = fun T => f ((1 / 3 : ℂ) * T) := by
    funext T
    congr 1
    ring
  rw [he]
  ext n
  rw [coeff_taylorPS, PowerSeries.coeff_rescale, coeff_taylorPS,
    HTGeometry.iteratedDeriv_comp_const_mul_of_ne f n (by norm_num : (1 / 3 : ℂ) ≠ 0),
    mul_zero]
  ring

private lemma shifted_zeta_analytic_zero :
    AnalyticAt ℂ (fun T : ℂ => zetaFunction (T / 3)) 0 := by
  have hf : AnalyticAt ℂ zetaFunction ((0 : ℂ) / 3) := by
    simpa only [zero_div] using zetaFunction_analytic_zero
  exact hf.comp (f := fun T : ℂ => T / 3) (by fun_prop)

lemma shiftedZetaQuotient_analytic_zero : AnalyticAt ℂ shiftedZetaQuotient 0 := by
  exact zetaFunction_analytic_zero.div shifted_zeta_analytic_zero
    (by simpa only [zero_div, zetaFunction_zero] using (one_ne_zero : (1 : ℂ) ≠ 0))

/-- The meromorphic quotient continues the formal quotient of the arithmetic zeta series. -/
theorem shiftedZetaQuotient_taylor :
    taylorPS shiftedZetaQuotient = shiftedZetaQuotientSeries := by
  have he : (fun T => shiftedZetaQuotient T * zetaFunction (T / 3)) =ᶠ[𝓝 (0 : ℂ)]
      zetaFunction := by
    have h₀ : zetaFunction ((0 : ℂ) / 3) ≠ 0 := by
      rw [zero_div, zetaFunction_zero]
      exact one_ne_zero
    filter_upwards [shifted_zeta_analytic_zero.continuousAt.eventually_ne h₀] with T hT
    exact div_mul_cancel₀ (zetaFunction T) hT
  have ht : taylorPS shiftedZetaQuotient * PowerSeries.rescale (1 / 3 : ℂ) zeta = zeta := by
    rw [← zetaFunction_taylor, ← taylorPS_divide_three,
      ← HTGeometry.taylorPS_mul_of_analyticAt_hardy
        shiftedZetaQuotient_analytic_zero shifted_zeta_analytic_zero]
    exact taylorPS_congr he
  change taylorPS shiftedZetaQuotient = zeta * (PowerSeries.rescale (1 / 3 : ℂ) zeta)⁻¹
  apply (PowerSeries.eq_mul_inv_iff_mul_eq ?_).mpr ht
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, zeta_constantCoeff]
  exact one_ne_zero

/-- The point-count zeta series converges to the rational zeta function near zero. -/
theorem zetaFunction_hasFPowerSeriesAt :
    HasFPowerSeriesAt zetaFunction
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n zeta)) 0 := by
  rw [← zetaFunction_taylor]
  simpa only [coeff_taylorPS] using zetaFunction_analytic_zero.hasFPowerSeriesAt

/-- The actual quotient coefficients converge locally to the function whose poles were proved. -/
theorem shiftedZetaQuotient_hasFPowerSeriesAt :
    HasFPowerSeriesAt shiftedZetaQuotient
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n shiftedZetaQuotientSeries)) 0 := by
  rw [← shiftedZetaQuotient_taylor]
  simpa only [coeff_taylorPS] using shiftedZetaQuotient_analytic_zero.hasFPowerSeriesAt

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
