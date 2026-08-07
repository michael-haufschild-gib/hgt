import GaloisForLFunctions.RHTower.ConstrainedProlateSignedSpectrum
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant

/-!
# Identification of signed and concentration prolate spectra

The concrete concentration operator is the energy operator of the signed compressed Fourier
block.  Since the absolute signed greedy spectrum of a compact self-adjoint operator is its
singular-value sequence, the concentration values are exactly the squares of the signed values,
with the same multiplicities and ordering.
-/

noncomputable section

namespace RHTower

/-- The actual concentration spectrum is the pointwise square of the actual signed spectrum. -/
theorem evenProlateConcentrationValue_eq_signedValue_sq
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    evenProlateConcentrationValue a n = evenProlateSignedValue a n ^ 2 := by
  change ContinuousLinearMap.svVal
      (ContinuousLinearMap.energyOp (evenTimeBandFourier a)) n =
    ContinuousLinearMap.sgVal (evenTimeBandFourier a) n ^ 2
  rw [← ContinuousLinearMap.singVal_sq]
  have habs := ContinuousLinearMap.abs_sgVal_eq_singVal
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a)) n
  rw [← habs, sq_abs]

/-- The concentration leakage and signed leakage therefore agree term by term. -/
theorem evenProlateLeakageValue_eq_signedValue_leakage
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    evenProlateLeakageValue a n = 1 - evenProlateSignedValue a n ^ 2 := by
  rw [evenProlateLeakageValue, evenProlateConcentrationValue_eq_signedValue_sq a ha n]

end RHTower

