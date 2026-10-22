import GaloisForLFunctions.HTGeometry.KrejcirikSourceChiralPseudospectrum
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaEscapingNonlocalChiralPolarization

/-!
# Krejčiřík bounds for arithmetic source chiralizations

This module specializes the universal positive-root similarity theorem to the Route-P
prime--Gamma matrices and to actual signed theta finite stages.  The resulting spectrum
identifications are stronger than equality of characteristic divisors.  For every nonempty
Route-P packet, equation (8) of arXiv:1402.1082 also controls the full norm-resolvent
pseudospectrum by the condition number of the source-defined positive root.
-/

open Complex Matrix Set
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator
open GaloisForLFunctions.HilbertMetric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Every Route-P escaped chiral operator has exactly the spectrum of its Hermitian dilation. -/
theorem routePPrimeGammaEscapingChiralOperator_spectrum_eq_dilation {N : ℕ}
    (k : ℕ) (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) :
    spectrum ℂ (routePPrimeGammaEscapingChiralOperator k R n kappa) =
      spectrum ℂ
        (sourceHermitianDilation (routePPrimeGammaCubicKernelMatrix R n kappa)) := by
  simpa only [routePPrimeGammaEscapingChiralOperator] using
    sourceEscapingChiralOperator_spectrum_eq_dilation k
      (routePPrimeGammaCubicKernelMatrix R n kappa)

/-- Equation (8) for every nonempty Route-P prime--Gamma packet. -/
theorem routePPrimeGammaEscapingChiralOperator_pseudospectrum_sandwich {N : ℕ}
    [NeZero N] (k : ℕ) (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ)
    (ε : PseudospectralScale) :
    normResolventPseudospectrum ℂ
          (ε.divConditionNumber
            (sourceEscapingNonlocalRootUnit k
              (routePPrimeGammaCubicKernelMatrix R n kappa))⁻¹)
          (sourceHermitianDilation (routePPrimeGammaCubicKernelMatrix R n kappa)) ⊆
        normResolventPseudospectrum ℂ ε
          (routePPrimeGammaEscapingChiralOperator k R n kappa) ∧
      normResolventPseudospectrum ℂ ε
          (routePPrimeGammaEscapingChiralOperator k R n kappa) ⊆
        normResolventPseudospectrum ℂ
          (ε.mulConditionNumber
            (sourceEscapingNonlocalRootUnit k
              (routePPrimeGammaCubicKernelMatrix R n kappa))⁻¹)
          (sourceHermitianDilation
            (routePPrimeGammaCubicKernelMatrix R n kappa)) := by
  simpa only [routePPrimeGammaEscapingChiralOperator] using
    sourceEscapingChiralOperator_pseudospectrum_sandwich k
      (routePPrimeGammaCubicKernelMatrix R n kappa) ε

namespace HedenmalmThetaSource

/-- Every actual signed theta finite stage has exactly its Hermitian dilation spectrum. -/
theorem thetaSourceEscapingChiralOperator_spectrum_eq_dilation (k : ℕ) :
    spectrum ℂ (thetaSourceEscapingChiralOperator k) =
      spectrum ℂ (sourceHermitianDilation (thetaSourceSignedFiniteMatrix k)) := by
  simpa only [thetaSourceEscapingChiralOperator] using
    sourceEscapingChiralOperator_spectrum_eq_dilation k
      (thetaSourceSignedFiniteMatrix k)

end HedenmalmThetaSource

end

end RHTower
