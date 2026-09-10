import GaloisForLFunctions.HTGeometry.GomesActualDerivativeReflectionAdjoin
import GaloisForLFunctions.HTGeometry.GomesDerivativePowerChainTransfers

/-!
# A concrete missing symmetry and the sharp actual generation boundary

The corpus's even-to-odd chain transfer commutes with D² but sends 1 to X.
Consequently no affine reflection together with D and the even formal functional
calculus can generate it. The exact surviving algebra is already classified.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- The existing even-to-odd chain transfer sends the constant polynomial to X. -/
theorem gomesEvenToOddChainTransfer_one :
    (gomesDerivativePowerChainTransfer K 2 1 0).val 1 = (X : K[X]) := by
  have h := gomesDerivativePowerChainTransfer_basis K 2 1 0 0 0
  simpa [gomesDividedMonomialBasis_apply] using h

/-- The concrete chain transfer lies outside the generated algebra for every center. -/
theorem gomesEvenToOddChainTransfer_not_mem_adjoin (c : K) :
    (gomesDerivativePowerChainTransfer K 2 1 0).val ∉ gomesPolynomialDerivativeReflectionAdjoin K c := by
  intro h
  have hc := ((gomesPolynomialDerivativeReflectionAdjoin_mem_iff K c _).mp h).2 1
  rw [map_one, gomesEvenToOddChainTransfer_one, Polynomial.derivative_X] at hc
  exact one_ne_zero hc

/-- A literal second-derivative symmetry is missing, with its distinguishing actual output specified. -/
theorem gomesPolynomialReflectionGenerated_missing_symmetry (c : K) :
    ∃ E : Module.End K K[X], E ∈ gomesPolynomialDerivativePowerCommutantAlgebra K 2 ∧
      E ∉ gomesPolynomialDerivativeReflectionAdjoin K c ∧ E 1 = X :=
  ⟨(gomesDerivativePowerChainTransfer K 2 1 0).val,
    (gomesDerivativePowerChainTransfer K 2 1 0).property,
    gomesEvenToOddChainTransfer_not_mem_adjoin K c, gomesEvenToOddChainTransfer_one K⟩

/-- The generated actual algebra is strictly smaller than the full second-derivative commutant. -/
theorem gomesPolynomialDerivativeReflectionAdjoin_lt_fullCommutant (c : K) :
    gomesPolynomialDerivativeReflectionAdjoin K c < gomesPolynomialDerivativePowerCommutantAlgebra K 2 := by
  apply lt_iff_le_and_ne.mpr
  constructor
  · intro E hE
    exact (gomesCentralizerSingleton_mem_iff K _ _).mpr
      ((gomesPolynomialDerivativeReflectionAdjoin_mem_iff K c E).mp hE).1.eq.symm
  · intro h
    apply gomesEvenToOddChainTransfer_not_mem_adjoin K c
    rw [h]
    exact (gomesDerivativePowerChainTransfer K 2 1 0).property

end GaloisForLFunctions.HTGeometry
