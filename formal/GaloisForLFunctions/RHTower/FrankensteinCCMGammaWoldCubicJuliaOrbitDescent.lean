import GaloisForLFunctions.RHTower.FrankensteinWoldCubicJuliaOrbitBudget
import GaloisForLFunctions.RHTower.FrankensteinCCMGammaWoldCubicSourcePolarization

/-!
# Literal completed-source descent to the Wold-regularized Julia orbit

This module composes two independent pieces of the Frankenstein chain.  The CCM/Gamma Schwarz
polarization produces the finite Wold cubic response from two separately gauged source poles.
The Wold cubic response cancels the inverse-cubic Route-P conormal scale, while complete
FE--Schwarz--Krein orbit symmetrization prevents the Julia environment pivot from erasing the
positive corner.

The theorem below performs this composition before the final conjugate-fibre source limit.  Its
limit is exactly the finite pivot-resistant Wold--Julia orbit response, retaining source clock,
Xi support, analytic multiplicity normalization, Schwarz orientation, and coefficient energy.
No completed-source order inequality is assumed.
-/

open Complex Matrix Filter Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Real physical readout of the first CCM/Gamma Schwarz landing, with the exact Route-P conormal
and four-orientation Julia normalizations. -/
def frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) : ℝ :=
  4 * Complex.normSq c *
    (-(frankensteinCCMGammaSchwarzCenteredCubicFirstLanding q N v).re *
      (1 / (4 * (xiRightCenteredZero q).re ^ 3)))

/-- **Completed-source Wold--Julia descent.**  The second source residue lands exactly in the
finite pivot-resistant regularized orbit response. -/
theorem tendsto_frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    Tendsto (frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding c q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N)) := by
  have hcomplex :=
    tendsto_frankensteinCCMGammaSchwarzCenteredCubicFirstLanding q N
  have hre : Tendsto (fun v : ℂ =>
      (frankensteinCCMGammaSchwarzCenteredCubicFirstLanding q N v).re)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceZeroHorizontalWoldPrimeClockCubicResponse q.1 N)) := by
    exact (Complex.continuous_re.tendsto
      (sourceZeroHorizontalWoldPrimeClockCubicResponse q.1 N : ℂ)).comp hcomplex
  have hneg : Tendsto (fun v : ℂ =>
      -(frankensteinCCMGammaSchwarzCenteredCubicFirstLanding q N v).re)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (-sourceZeroHorizontalWoldPrimeClockCubicResponse q.1 N)) := hre.neg
  have hreg := hneg.mul_const
    (1 / (4 * (xiRightCenteredZero q).re ^ 3))
  have horbit := hreg.const_mul (4 * Complex.normSq c)
  convert horbit using 1
  · funext v
    rw [frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding]
  · rw [sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse,
      sourceZeroHorizontalWoldRegularizedRoutePConormalResponse]

end

end RHTower
