import GaloisForLFunctions.HTGeometry.CountableDifferentialPattern
import GaloisForLFunctions.HTGeometry.PolynomialCoefficientDifferentialFreeness
import GaloisForLFunctions.HTGeometry.BoundaryCarrierTranslationFreeness

/-!
# The zero relation realizes every pattern-relation interface

Each finite-pattern relation interface asserts that a coefficient family annihilates an evaluated
jet packet on a common upper domain.  The zero family does, so none of the rigidity theorems is
vacuous: they say exactly that the zero relation is the only one.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem patternRelationHolds_zero {Γ : Type*} (shiftValue : Γ → ℂ)
    (p : FiniteDifferentialPattern Γ) (u : PrimeLogBoundedGauge) :
    PatternRelationHolds shiftValue p u 0 := by
  intro z _
  simp

theorem polynomialCoefficientDifferentialRelationHolds_zero
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ)
    (shiftCode : Fin m → Γ) (orders : Fin m → ℕ) (u : PrimeLogBoundedGauge) :
    PolynomialCoefficientDifferentialRelationHolds shiftValue shiftCode orders u 0 := by
  intro z _
  simp

theorem probabilityCarrierExpandedPatternRelationHolds_zero
    {row κ ι : Type} [Fintype κ] [Fintype ι]
    (nu : ProbabilityMeasure ℝ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (shift : InjectiveShiftConfiguration ι) :
    probabilityCarrierExpandedPatternRelationHolds (row := row) nu degree orders
      exponent shift 0 := by
  intro packet _ r
  simp

end GaloisForLFunctions.HTGeometry
