import GaloisForLFunctions.RHTower.DeningerArithmeticSpectralLine

/-!
# Xi explicit-formula Lefschetz comparison for arbitrary positive-time tests

This module combines three independently proved Euler-line identities:

* the multiplicity-exact Xi spectral line;
* the von-Mangoldt prime-power line;
* the archimedean and endpoint line.

The result is the analytic equality predicted by Deninger's Proposition 3.2 on `(0,∞)`.
No RH, zero simplicity, special test family, or cohomological positivity assumption is used.
Its middle trace distribution is defined from `XiZeroCopy`. The separate module
`DeningerMeyerFlowLefschetz` identifies it with the operator trace of compact smooth averages
of the original Meyer flow on its faithful full-Hasse Hilbert completion.
-/

open Complex MeasureTheory
open scoped BigOperators

noncomputable section

namespace RHTower

theorem integral_deningerTimeTestLaplace_mul_logDeriv_xi_eq_arch_sub_prime
    (φ : DeningerTimeTestFunction) :
    (∫ ξ : ℝ,
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
          logDeriv xi
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
      (∫ ξ : ℝ,
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
          logDeriv archFactor
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) -
        ∫ ξ : ℝ,
          deningerTimeTestLaplace φ
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
            LSeries
              (fun n =>
                (ArithmeticFunction.vonMangoldt n : ℂ))
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  have harch :=
    integrable_deningerTimeTestLaplace_mul_logDeriv_archFactor
      φ
  have hprime :=
    integrable_deningerTimeTestLaplace_mul_vonMangoldtLSeries
      φ
  rw [show
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
          logDeriv xi
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
        fun ξ : ℝ =>
          deningerTimeTestLaplace φ
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
            logDeriv archFactor
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I) -
          deningerTimeTestLaplace φ
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
            LSeries
              (fun n =>
                (ArithmeticFunction.vonMangoldt n : ℂ))
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I) by
    funext ξ
    rw [show
        (((3 / 2 : ℝ) : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) * I) =
            deningerXiRightEulerPoint ξ by
      rfl,
      logDeriv_xi_deningerXiRightEulerPoint_eq]
    ring,
    integral_sub harch hprime]

theorem deningerArithmeticScalarExplicitFormula_proved :
    DeningerArithmeticScalarExplicitFormula := by
  intro φ
  have hspectral :=
    integral_deningerTimeTestLaplace_mul_logDeriv_xi φ
  rw [
    integral_deningerTimeTestLaplace_mul_logDeriv_xi_eq_arch_sub_prime,
    integral_deningerTimeTestLaplace_mul_logDeriv_archFactor,
    integral_deningerTimeTestLaplace_mul_vonMangoldtLSeries_eq_primeDistribution
      φ (by norm_num : (1 : ℝ) < 3 / 2)] at hspectral
  linear_combination hspectral

/--
Unconditional Xi explicit-formula distributional identity predicted by Deninger's program, on the
full space of smooth compactly supported positive-time tests.  This theorem does not identify the
left side with a source-flow operator trace; that transport is proved in
`DeningerMeyerFlowLefschetz` on the faithful Hasse completion.
-/
theorem deningerArithmeticDistributionalLefschetz :
    deningerArithmeticAlternatingTraceDistribution =
      deningerPrimeArchimedeanLefschetzDistribution :=
  deningerArithmeticDistributionalLefschetz_iff_scalarExplicitFormula.mpr
    deningerArithmeticScalarExplicitFormula_proved

end RHTower
