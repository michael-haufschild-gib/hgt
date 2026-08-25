/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraTowerCentralizer
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryInflation
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerAdditive

/-!
# Brauer realization commutes with cyclic Galois inflation

The split-centralizer theorem identifies the Brauer class of an orientation-corrected upper
cyclic algebra with the lower cyclic algebra.  It follows that the selected cyclic Brauer map
commutes with the oriented periodic norm-quotient transition.

Literal carry cocycles compute genuine group-cohomological inflation.  Conjugating the selected
Brauer map by the explicit periodic-to-carry automorphism therefore gives a carry-normalized
Brauer realization that commutes with genuine inflation on every finite cyclic norm quotient.
This is the finite-layer compatibility needed to descend unramified local `H²` invariants to a
Brauer-valued directed limit.
-/

open CategoryTheory Representation

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

theorem cyclicGaloisH2Parameter_brauerClass_tower_inflation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (a : Additive Kˣ) :
    brauerClass (cyclicGaloisH2ParameterCSA K M
        (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a)) =
      brauerClass (cyclicGaloisH2ParameterCSA K L a) := by
  change brauerClass (cyclicGaloisAlgebraCSA K M
      (((((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a).toMul : K))
      _) = brauerClass (cyclicGaloisAlgebraCSA K L (a.toMul : K) _)
  simpa using cyclicGaloisAlgebra_brauerClass_tower_inflation K L M
    (a.toMul : K) a.toMul.ne_zero

theorem cyclicGaloisH2BrauerMap_orientedNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2BrauerMap K M
        (cyclicGaloisH2OrientedNormQuotientTransition K L M z) =
      cyclicGaloisH2BrauerMap K L z := by
  obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  rw [cyclicGaloisH2OrientedNormQuotientTransition_baseProjection]
  rw [← cyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection
      K M _ _ rfl]
  rw [← cyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection
      K L _ _ rfl]
  exact cyclicGaloisH2Parameter_brauerClass_tower_inflation K L M a

noncomputable def cyclicGaloisCarryNormalizedBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    cyclicGaloisH2 K L → BrauerGroup K :=
  fun z => cyclicGaloisH2BrauerMap K L
    ((cyclicGaloisH2PeriodicCarryAutomorphism K L).symm z)

@[simp] theorem cyclicGaloisCarryNormalizedBrauerMap_carryClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (a : Additive Kˣ) :
    cyclicGaloisCarryNormalizedBrauerMap K L (cyclicGaloisCarryH2Class K L a) =
      brauerClass (cyclicGaloisH2ParameterCSA K L a) := by
  rw [cyclicGaloisCarryNormalizedBrauerMap,
    ← cyclicGaloisH2PeriodicCarryAutomorphism_baseProjection K L a,
    AddEquiv.symm_apply_apply]
  exact (cyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection
    K L a (cyclicGaloisH2BaseProjection K L a) rfl).symm

theorem cyclicGaloisCarryNormalizedBrauerMap_genuineInflation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)]
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisCarryNormalizedBrauerMap K M
        ((groupCohomology.map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
          (galoisTowerUnitsRepresentationHom K L M) 2).hom z) =
      cyclicGaloisCarryNormalizedBrauerMap K L z := by
  obtain ⟨a, rfl⟩ := cyclicGaloisCarryH2Class_surjective K L z
  rw [cyclicGaloisCarryH2Class_inflation,
    cyclicGaloisCarryNormalizedBrauerMap_carryClass,
    cyclicGaloisCarryNormalizedBrauerMap_carryClass]
  exact cyclicGaloisH2Parameter_brauerClass_tower_inflation K L M a

/-- Carry-normalized Brauer realization as an additive homomorphism. -/
noncomputable def cyclicGaloisCarryNormalizedBrauerAddHom
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    cyclicGaloisH2 K L →+ BrauerGroup K :=
  (cyclicGaloisH2BrauerAddHom K L).comp
    (cyclicGaloisH2PeriodicCarryAutomorphism K L).symm.toAddMonoidHom

@[simp] theorem cyclicGaloisCarryNormalizedBrauerAddHom_apply
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisCarryNormalizedBrauerAddHom K L z =
      cyclicGaloisCarryNormalizedBrauerMap K L z := rfl

/-- Genuine cyclic inflation maps form a cocone under carry-normalized Brauer realization. -/
theorem cyclicGaloisCarryNormalizedBrauerAddHom_comp_genuineInflation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)] :
    (cyclicGaloisCarryNormalizedBrauerAddHom K M).comp
        (groupCohomology.map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
          (galoisTowerUnitsRepresentationHom K L M) 2).hom.toAddMonoidHom =
      cyclicGaloisCarryNormalizedBrauerAddHom K L := by
  ext z
  exact cyclicGaloisCarryNormalizedBrauerMap_genuineInflation K L M z

/-- Carry-normalized Brauer realization of finite continuous cyclic `H²`. -/
noncomputable def finiteGaloisContinuousCarryNormalizedBrauerAddHom
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    continuousGaloisH2 K L →+ BrauerGroup K :=
  (cyclicGaloisCarryNormalizedBrauerAddHom K L).comp
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).toAddMonoidHom

/-- Finite continuous cyclic inflation maps form a Brauer-valued cocone. -/
theorem finiteGaloisContinuousCarryNormalizedBrauerAddHom_comp_inflation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)] :
    (finiteGaloisContinuousCarryNormalizedBrauerAddHom K M).comp
        (finiteGaloisContinuousH2Inflation K L M) =
      finiteGaloisContinuousCarryNormalizedBrauerAddHom K L := by
  ext z
  change cyclicGaloisCarryNormalizedBrauerAddHom K M
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M
        (finiteGaloisContinuousH2Inflation K L M z)) =
    cyclicGaloisCarryNormalizedBrauerAddHom K L
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)
  rw [finiteGaloisContinuousH2Inflation_toOrdinary_apply]
  exact cyclicGaloisCarryNormalizedBrauerMap_genuineInflation K L M
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)

end

end GaloisForLFunctions.HTGeometry.ABHN
