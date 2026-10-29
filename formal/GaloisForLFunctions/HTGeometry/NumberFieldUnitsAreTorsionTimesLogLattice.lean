import GaloisForLFunctions.HTGeometry.NumberFieldUnitLogFundamentalDomain

/-!
# Global units as torsion times their logarithm lattice

Dirichlet's unique torsion/fundamental-unit decomposition and the actual unit-lattice basis
identify global units with torsion units times lattice points. The inverse has an explicit
fundamental-unit product, and its logarithmic embedding is exactly the lattice coordinate.
Completing that coordinate recovers the full weighted-zero place-logarithm profile.
-/

noncomputable section
open NumberField
open NumberField.Units.dirichletUnitTheorem
open scoped Classical
namespace GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] [NumberField K]

/-- Form a global unit from a torsion unit and fundamental-unit exponents. -/
def numberFieldUnitFromTorsionExponents
    (p : Units.torsion K × (Fin (Units.rank K) → ℤ)) : (𝓞 K)ˣ :=
  p.1 * ∏ i, (Units.fundSystem K i) ^ p.2 i

/-- Uniqueness in Dirichlet's unit theorem makes the product map injective. -/
theorem numberFieldUnitFromTorsionExponents_injective :
    Function.Injective (numberFieldUnitFromTorsionExponents (K := K)) := by
  intro p q h
  obtain ⟨r, _, hr⟩ := Units.exist_unique_eq_mul_prod K
    (numberFieldUnitFromTorsionExponents p)
  exact (hr p rfl).trans (hr q h).symm

/-- Every global unit has a torsion factor and fundamental-unit exponents. -/
theorem numberFieldUnitFromTorsionExponents_surjective :
    Function.Surjective (numberFieldUnitFromTorsionExponents (K := K)) := by
  intro u
  obtain ⟨p, hp, _⟩ := Units.exist_unique_eq_mul_prod K u
  exact ⟨p, hp.symm⟩

/-- Global units are exactly torsion units times points of their actual logarithm lattice. -/
def numberFieldUnitsEquivTorsionLogLattice :
    (𝓞 K)ˣ ≃ Units.torsion K × Units.unitLattice K :=
  (Equiv.ofBijective (numberFieldUnitFromTorsionExponents (K := K))
    ⟨numberFieldUnitFromTorsionExponents_injective,
      numberFieldUnitFromTorsionExponents_surjective⟩).symm.trans
    (Equiv.prodCongr (Equiv.refl _) (Units.basisUnitLattice K).equivFun.symm.toEquiv)

/-- The inverse equivalence has an explicit product of fundamental units. -/
theorem numberFieldUnitsEquivTorsionLogLattice_symm_apply
    (ζ : Units.torsion K) (l : Units.unitLattice K) :
    (numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (ζ, l) =
      (ζ : (𝓞 K)ˣ) * ∏ i, (Units.fundSystem K i) ^
        ((Units.basisUnitLattice K).equivFun l i) := rfl

/-- The logarithm of a reconstructed unit is precisely its lattice coordinate. -/
theorem logEmbedding_numberFieldUnitsEquivTorsionLogLattice_symm
    (ζ : Units.torsion K) (l : Units.unitLattice K) :
    Units.logEmbedding K (Additive.ofMul
      ((numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (ζ, l))) =
      (l : logSpace K) := by
  rw [numberFieldUnitsEquivTorsionLogLattice_symm_apply, ofMul_mul, map_add,
    logEmbedding_eq_zero_iff.mpr ζ.2, zero_add, ofMul_prod, map_sum]
  simp_rw [ofMul_zpow, map_zsmul, Units.logEmbedding_fundSystem]
  change (∑ i, (Units.basisUnitLattice K).repr l i •
    ((Units.basisUnitLattice K i : Units.unitLattice K) : logSpace K)) = _
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using
    congrArg (fun x : Units.unitLattice K => (x : logSpace K))
      ((Units.basisUnitLattice K).sum_repr l)

/-- The second coordinate of the decomposition is the actual unit logarithm. -/
theorem numberFieldUnitsEquivTorsionLogLattice_logEmbedding (u : (𝓞 K)ˣ) :
    ((numberFieldUnitsEquivTorsionLogLattice (K := K) u).2 : logSpace K) =
      Units.logEmbedding K (Additive.ofMul u) := by
  have h := logEmbedding_numberFieldUnitsEquivTorsionLogLattice_symm
    (numberFieldUnitsEquivTorsionLogLattice u).1
    (numberFieldUnitsEquivTorsionLogLattice u).2
  rw [Prod.mk.eta, Equiv.symm_apply_apply] at h
  exact h.symm

/-- Completing the lattice coordinate gives the full place logarithm of the actual unit. -/
theorem numberFieldWeightedLogProfile_unitLatticeCoordinate (u : (𝓞 K)ˣ) :
    numberFieldWeightedLogProfile
        ((numberFieldUnitsEquivTorsionLogLattice (K := K) u).2 : logSpace K) =
      numberFieldUnitPlaceLogEmbeddings u := by
  rw [numberFieldUnitsEquivTorsionLogLattice_logEmbedding,
    numberFieldWeightedLogProfile_logEmbedding]

end GaloisForLFunctions.HTGeometry
