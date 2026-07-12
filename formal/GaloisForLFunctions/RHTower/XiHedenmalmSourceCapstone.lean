import GaloisForLFunctions.RHTower.XiHedenmalmReciprocalOperator
import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate

/-!
# Source-to-Hilbert capstone for the Hedenmalm theta pair

The continued prime--archimedean one-Cauchy diagonal sign is an exact source-side RH criterion.
The actual Hedenmalm theta eigenfunction evaluations are complete in the multiplicity-exact Xi
carrier exactly when every Xi zero is simple. Combining the two closed equivalences gives a fully
concrete source-to-Hilbert chain with no assumed positivity, spectral, or approximation interface.
-/

namespace RHTower

noncomputable section

open Complex

/-- The source-side criterion with its formula exposed: the continued prime--Gamma relative trace
has nonnegative conjugate divided-difference diagonal throughout the pole-free centered upper
half-strip exactly when RH holds. -/
theorem continuedPrimeArchUpperCauchyFormula_iff_riemannHypothesis :
    ((∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * I) ≠ 0 →
        0 ≤ ((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) -
          continuedPrimeArchSourceRelativeTrace z) /
            (z - (starRingEnd ℂ) z)).re)) ↔
      RiemannHypothesis := by
  simpa only [ContinuedPrimeArchUpperCauchyDiagonalNonnegative] using
    continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis

/-- Fully exposed source-to-eigenfamily law. The displayed prime--Gamma inequality and density of
the actual regular theta solutions are together equivalent to RH plus simplicity. -/
theorem continuedPrimeArchFormula_and_thetaComplete_iff_rh_and_simple :
    ((∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
        riemannZeta (1 / 2 + z * I) ≠ 0 →
          0 ≤ ((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) -
            continuedPrimeArchSourceRelativeTrace z) /
              (z - (starRingEnd ℂ) z)).re) ∧
      Dense (xiThetaEigenAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2))) ↔
      RiemannHypothesis ∧ XiZerosSimple := by
  rw [continuedPrimeArchUpperCauchyFormula_iff_riemannHypothesis,
    xiThetaEigenAlgebraicSubspace_dense_iff_simple]

/-- The source-side prime--Gamma sign together with actual theta-eigenfunction completeness is
equivalent to RH plus simplicity. No hypothesis is assumed. -/
theorem continuedPrimeArch_and_thetaComplete_iff_rh_and_simple :
    (ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      Dense (xiThetaEigenAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2))) ↔
      RiemannHypothesis ∧ XiZerosSimple := by
  rw [continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis,
    xiThetaEigenAlgebraicSubspace_dense_iff_simple]

/-- The same concrete source condition is equivalent to existence of a conservative
divisor-supported Hedenmalm metric. -/
theorem continuedPrimeArch_and_thetaComplete_iff_exists_conservative_metric :
    (ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      Dense (xiThetaEigenAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2))) ↔
      ∃ c : XiRealDivisorWeight, XiThetaMetricConservative c := by
  rw [continuedPrimeArch_and_thetaComplete_iff_rh_and_simple,
    ← exists_conservative_xiThetaMetric_iff_rh_and_simple]

/-- Source-to-operator form: the prime--Gamma sign and theta completeness are equivalent to
self-adjointness of the compact reciprocal Xi operator together with completeness of its actual
Hedenmalm eigenfamily. -/
theorem continuedPrimeArch_and_thetaComplete_iff_selfAdjoint_and_eigenComplete :
    (ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      Dense (xiThetaEigenAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2))) ↔
      IsSelfAdjoint xiReciprocalOperator ∧
        Dense (xiThetaEigenAlgebraicSubspace :
          Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
  rw [continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis,
    xiReciprocalOperator_isSelfAdjoint_iff_rh]

end

end RHTower
