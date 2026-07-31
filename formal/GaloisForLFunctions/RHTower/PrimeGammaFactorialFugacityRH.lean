import GaloisForLFunctions.RHTower.PrimeGammaFactorialFugacityBoundary
import GaloisForLFunctions.RHTower.RiemannComplexModularCharacterLaw

/-!
# Conditional factorial-fugacity RH consumer

The critical Gamma factorial field has a sharp summability wall at fugacity
`lambda = 1`.  A divisor point of horizontal rate
`q = rho.re - 1 / 2` produces reciprocal rates `1 + 2q` and `1 - 2q`.
If a source-defined dagger identifies those two fibres while preserving
summability class, the sharp wall forces `q = 0`.

The theorem below exposes that dagger/summability equivalence as an explicit
unproved hypothesis.  It does not construct the required Xi landing.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- **Conditional RH consumer.** If every Xi-zero fibre has a dagger
preserving the summability class of its two reciprocal factorial fugacities,
then every zero lies on the critical line. -/
theorem riemannHypothesis_of_reflectedFugacitySummability_equiv
    (hdagger :
      ∀ rho, xi rho = 0 →
        (Summable
            (primeGammaFactorialFugacityBoundaryWeight
              (1 + 2 * (rho.re - 1 / 2))) ↔
          Summable
            (primeGammaFactorialFugacityBoundaryWeight
              (1 - 2 * (rho.re - 1 / 2))))) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hq : rho.re - 1 / 2 = 0 :=
    (reflectedFugacitySummability_equiv_iff
      (rho.re - 1 / 2)).mp (hdagger rho hzero)
  have hline : rho.re = 1 / 2 := by linarith
  exact (ne_of_gt (mem_rightHalf.mp hrho)) hline

end

end RHTower
