/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisH2TorsionCharacter
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2TorsionBrauer

/-!
# Torsion `H²` phases and cyclic Brauer representatives

A finite cyclic continuous `H²` layer carries a faithful finite circle character after choosing
its torsion invariant.  If that phase is one, the class is zero, so the associated cyclic Brauer
representative is split.  Contrapositively, a non-split representative has nontrivial phase.

No converse is claimed: it would require an injective comparison from the particular cyclic
cohomology parameterization to the Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- A unit torsion `H²` phase has split cyclic Brauer representative. -/
theorem finiteGaloisContinuousCyclicH2BrauerMap_eq_split_of_torsionStdPhase_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : continuousGaloisUnitCohomology 2 K L)
    (hz : continuousGaloisH2TorsionStdAddChar K L n hn e z = 1) :
    finiteGaloisContinuousCyclicH2BrauerMap K L z = brauerSplitClass K := by
  rw [continuousGaloisH2TorsionStdAddChar_eq_one_iff_eq_zero K L n hn e] at hz
  rw [hz]
  exact finiteGaloisContinuousCyclicH2BrauerMap_zero_eq_split K L

/-- A non-split cyclic Brauer representative has nontrivial torsion `H²` phase. -/
theorem finiteGaloisContinuousCyclicH2BrauerMap_ne_split_implies_torsionStdPhase_ne_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : continuousGaloisUnitCohomology 2 K L)
    (hz : finiteGaloisContinuousCyclicH2BrauerMap K L z ≠ brauerSplitClass K) :
    continuousGaloisH2TorsionStdAddChar K L n hn e z ≠ 1 := by
  intro hphase
  exact hz (finiteGaloisContinuousCyclicH2BrauerMap_eq_split_of_torsionStdPhase_eq_one
    K L n hn e z hphase)

/-- A unit torsion `H²` phase maps to the split representative through the finite torsion
invariant parameterization. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_eq_split_of_torsionStdPhase_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : continuousGaloisUnitCohomology 2 K L)
    (hz : continuousGaloisH2TorsionStdAddChar K L n hn e z = 1) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e (e z) =
      brauerSplitClass K := by
  rw [continuousGaloisH2TorsionStdAddChar_eq_one_iff_eq_zero K L n hn e] at hz
  rw [hz]
  rw [e.map_zero]
  exact finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_zero_eq_split K L n e

/-- A non-split finite torsion-invariant representative has nontrivial `H²` phase. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_ne_split_implies_torsionStdPhase_ne_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : continuousGaloisUnitCohomology 2 K L)
    (hz : finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e (e z) ≠
      brauerSplitClass K) :
    continuousGaloisH2TorsionStdAddChar K L n hn e z ≠ 1 := by
  intro hphase
  exact hz
    (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_eq_split_of_torsionStdPhase_eq_one
      K L n hn e z hphase)

end

end GaloisForLFunctions.HTGeometry.ABHN
