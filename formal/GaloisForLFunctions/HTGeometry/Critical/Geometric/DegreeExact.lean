import GaloisForLFunctions.HTGeometry.CriticalArcFibreSourceAlgHom
import GaloisForLFunctions.HTGeometry.Critical.Geometric.SheetUpperBound

/-!
# Exact degree of the actual critical function-field extension

The exact common-scale arc fibre injects into the observation-field embeddings of the actual source
field, giving the lower degree bound.  The normal-closure valuative reduction gives the opposite
bound.  Together they identify the actual extension degree and actual geometric sheet count with
the critical binomial multiplicity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 100000

/-- Exact arc-fibre multiplicity is a lower bound for the degree of the actual critical source
extension. -/
theorem criticalHorizonMultiplicity_le_finrank_criticalSourceField
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalHorizonMultiplicity m n ≤
      Module.finrank (criticalObservationField K m n) (criticalSourceField K m n) := by
  letI : Algebra (criticalObservationField K m n) (CriticalArcLaurentField K m n) :=
    criticalObservationArcLaurentFieldAlgebra K hm hn
  letI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  calc
    criticalHorizonMultiplicity m n = Nat.card (CriticalArcFibre K m n) :=
      (natCard_criticalArcFibre K hm hn).symm
    _ ≤ Nat.card (criticalSourceField K m n →ₐ[criticalObservationField K m n]
        CriticalArcLaurentField K m n) :=
      Nat.card_le_card_of_injective (criticalArcFibreToSourceAlgHom K hm hn)
        (criticalArcFibreToSourceAlgHom_injective K hm hn)
    _ ≤ Module.finrank (criticalObservationField K m n) (criticalSourceField K m n) :=
      card_algHom_le_finrank (criticalObservationField K m n)
        (criticalSourceField K m n) (CriticalArcLaurentField K m n)

/-- **Exact degree theorem for the actual critical function fields.** -/
theorem finrank_criticalSourceField_eq_criticalHorizonMultiplicity
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Module.finrank (criticalObservationField K m n) (criticalSourceField K m n) =
      criticalHorizonMultiplicity m n := by
  exact le_antisymm
    (finrank_criticalSourceField_le_criticalHorizonMultiplicity K hm hn)
    (criticalHorizonMultiplicity_le_finrank_criticalSourceField K hm hn)

/-- The number of actual geometric sheets is exactly the critical binomial multiplicity. -/
theorem natCard_criticalGeometricSheet_eq_criticalHorizonMultiplicity
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalGeometricSheet K m n) = criticalHorizonMultiplicity m n := by
  rw [natCard_criticalGeometricSheet_eq_finrank K hm hn,
    finrank_criticalSourceField_eq_criticalHorizonMultiplicity K hm hn]

end

end GaloisForLFunctions.HTGeometry
