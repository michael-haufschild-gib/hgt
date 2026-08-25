import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerFaithful
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2TorsionBrauer

/-!
# Faithfulness of finite continuous cyclic `H²` in the Brauer group

The finite continuous-to-ordinary comparison is an additive equivalence.  Composing it with the
faithful cyclic `H²` Brauer realization shows that finite continuous `H²`, and every finite
torsion-invariant coordinate on it, embeds faithfully into the Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- A finite continuous cyclic `H²` class has split Brauer image exactly when it is zero. -/
theorem finiteGaloisContinuousCyclicH2BrauerMap_eq_split_iff
    (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousCyclicH2BrauerMap K L z = brauerSplitClass K ↔ z = 0 := by
  change cyclicGaloisH2BrauerMap K L
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) = brauerSplitClass K ↔ z = 0
  rw [cyclicGaloisH2BrauerMap_eq_split_iff]
  exact (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).map_eq_zero_iff

/-- A torsion-coordinate cyclic Brauer representative is split exactly at zero invariant. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_eq_split_iff
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z =
      brauerSplitClass K ↔ z = 0 := by
  change finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm z) =
    brauerSplitClass K ↔ z = 0
  rw [finiteGaloisContinuousCyclicH2BrauerMap_eq_split_iff]
  exact e.symm.map_eq_zero_iff

/-- Every finite torsion-invariant coordinate embeds injectively into the Brauer group. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_injective
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    Function.Injective
      (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e) := by
  intro x y hxy
  change cyclicGaloisH2BrauerMap K L
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L (e.symm x)) =
    cyclicGaloisH2BrauerMap K L
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L (e.symm y)) at hxy
  apply e.symm.injective
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).injective
  exact cyclicGaloisH2BrauerAddHom_injective K L hxy

end

end GaloisForLFunctions.HTGeometry.ABHN
