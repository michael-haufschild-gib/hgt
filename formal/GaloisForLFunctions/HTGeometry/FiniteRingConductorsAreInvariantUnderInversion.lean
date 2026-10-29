import GaloisForLFunctions.HTGeometry.FiniteRingCharactersHavePrimitiveConductors

/-!
# Inversion preserves finite-ring conductors

A unit character descends through an ideal exactly when it is trivial on
its unit congruence kernel. Inversion preserves this condition, hence
preserves the greatest descent ideal defining the conductor.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.FiniteRing

variable {R C : Type*} [CommRing R] [Finite R] [Field C]

/-- Inverting a multiplicative character preserves every quotient through which it descends. -/
theorem factorsThrough_inv_iff (χ : MulChar R C) (J : Ideal R) :
    FactorsThrough χ⁻¹ J ↔ FactorsThrough χ J := by
  rw [factorsThrough_iff, factorsThrough_iff]
  simp only [MulChar.inv_apply_eq_inv', inv_eq_one]

/-- A finite multiplicative character and its inverse have the same conductor ideal. -/
theorem conductorIdeal_inv (χ : MulChar R C) : conductorIdeal χ⁻¹ = conductorIdeal χ := by
  apply le_antisymm
  · exact (factorsThrough_iff_le_conductorIdeal χ _).mp
      ((factorsThrough_inv_iff χ _).mp (factorsThrough_conductorIdeal χ⁻¹))
  · exact (factorsThrough_iff_le_conductorIdeal χ⁻¹ _).mp
      ((factorsThrough_inv_iff χ _).mpr (factorsThrough_conductorIdeal χ))

end GaloisForLFunctions.FiniteRing

#print axioms GaloisForLFunctions.FiniteRing.conductorIdeal_inv
