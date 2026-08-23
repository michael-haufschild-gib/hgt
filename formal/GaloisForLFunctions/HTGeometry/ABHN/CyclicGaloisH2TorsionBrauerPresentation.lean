/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2TorsionBrauer

/-!
# Finite `ℚ/ℤ`-level presentation of cyclic relative Brauer classes

For a finite cyclic Galois extension whose continuous degree-two unit cohomology is identified
with `ℚ/ℤ[n]`, each torsion value selects a cyclic Brauer class.  The selector is not claimed to
be additive: that remains the cyclic tensor-product comparison.  Nevertheless its free additive
extension is surjective onto the cyclic Brauer subgroup, and quotienting by its exact relation
subgroup gives that subgroup.  This is an invariant-indexed, closed local finite-level
presentation suitable for a later local-class-field-theory comparison.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- The finite torsion local-invariant coordinate group, transported to ordinary cyclic `H²`. -/
noncomputable def finiteGaloisContinuousCyclicH2TorsionInvariantToCyclicH2AddEquiv
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    ratModIntNTorsion n ≃+ cyclicGaloisH2 K L :=
  e.symm.trans (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L)

/-- The selected torsion-indexed Brauer representative is the ordinary cyclic `H²` selector
after transporting its `ℚ/ℤ[n]` coordinate. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_eq_cyclicGaloisH2BrauerMap
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z =
      cyclicGaloisH2BrauerMap K L
        (finiteGaloisContinuousCyclicH2TorsionInvariantToCyclicH2AddEquiv K L n e z) := rfl

/-- Reindexing by finite local-invariant values neither loses nor adds selected cyclic Brauer
classes. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_range_eq_cyclicGaloisH2BrauerMap_range
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    Set.range (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e) =
      Set.range (cyclicGaloisH2BrauerMap K L) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨finiteGaloisContinuousCyclicH2TorsionInvariantToCyclicH2AddEquiv K L n e z,
      finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_eq_cyclicGaloisH2BrauerMap K L n e z⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨q, hq⟩ :=
      (finiteGaloisContinuousCyclicH2TorsionInvariantToCyclicH2AddEquiv K L n e).surjective z
    refine ⟨q, ?_⟩
    rw [finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_eq_cyclicGaloisH2BrauerMap,
      hq]

/-- Free additive presentation of the cyclic Brauer subgroup by finite `ℚ/ℤ[n]` local-invariant
values. -/
noncomputable def finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    FreeAbelianGroup (ratModIntNTorsion n) →+ cyclicGaloisBrauerSubgroup K L :=
  FreeAbelianGroup.lift
    (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerSubgroupMap K L n e)

/-- A free torsion generator maps to its selected cyclic Brauer representative. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_apply_of
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation K L n e
      (FreeAbelianGroup.of z) =
        finiteGaloisContinuousCyclicH2TorsionInvariantBrauerSubgroupMap K L n e z := by
  change FreeAbelianGroup.lift
    (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerSubgroupMap K L n e)
      (FreeAbelianGroup.of z) = _
  exact FreeAbelianGroup.lift_apply_of
    (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerSubgroupMap K L n e) z

/-- On ambient Brauer classes, a free torsion generator maps to its selected representative. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_apply_of_coe
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    ((finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation K L n e
      (FreeAbelianGroup.of z) : cyclicGaloisBrauerSubgroup K L) : BrauerGroup K) =
      finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z := by
  rw [finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_apply_of]
  rfl

/-- Finite `ℚ/ℤ[n]` local-invariant values generate the full cyclic Brauer subgroup after free
additive extension. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_surjective
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    Function.Surjective
      (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation K L n e) := by
  intro x
  have hx : (x : BrauerGroup K) ∈ AddSubgroup.closure
      (Set.range (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e)) := by
    rw [finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_range_eq_cyclicGaloisH2BrauerMap_range,
      ← cyclicGaloisBrauerSubgroup_eq_closure_range_cyclicGaloisH2BrauerMap]
    exact x.property
  have hle : AddSubgroup.closure
      (Set.range (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e)) ≤
      ((cyclicGaloisBrauerSubgroup K L).subtype.comp
        (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation K L n e)).range := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨z, rfl⟩
    refine ⟨FreeAbelianGroup.of z, ?_⟩
    exact finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_apply_of_coe
      K L n e z
  rcases hle hx with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact hw

/-- Exact relation subgroup for the finite torsion local-invariant presentation. -/
noncomputable def finiteGaloisContinuousCyclicH2TorsionInvariantBrauerRelationSubgroup
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    AddSubgroup (FreeAbelianGroup (ratModIntNTorsion n)) :=
  (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation K L n e).ker

/-- Quotienting the finite torsion local-invariant presentation by its exact relation subgroup
recovers the cyclic Brauer subgroup. -/
noncomputable def finiteGaloisContinuousCyclicH2TorsionInvariantBrauerPresentationQuotientAddEquiv
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    FreeAbelianGroup (ratModIntNTorsion n) ⧸
      finiteGaloisContinuousCyclicH2TorsionInvariantBrauerRelationSubgroup K L n e ≃+
      cyclicGaloisBrauerSubgroup K L :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation K L n e)
    (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_surjective K L n e)

/-- Opposite torsion values cancel under the finite local-invariant free presentation. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_inverse_pair
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation K L n e
      (FreeAbelianGroup.of z + FreeAbelianGroup.of (-z)) = 0 := by
  rw [map_add, finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_apply_of,
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_apply_of]
  apply Subtype.ext
  change finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z +
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e (-z) = brauerSplitClass K
  rw [← finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_brauerTensorNeg]
  exact add_neg_cancel _

/-- The formal inverse pair belongs to the exact finite torsion local-invariant relation
subgroup. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauer_inverse_pair_mem_relation
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    FreeAbelianGroup.of z + FreeAbelianGroup.of (-z) ∈
      finiteGaloisContinuousCyclicH2TorsionInvariantBrauerRelationSubgroup K L n e := by
  exact finiteGaloisContinuousCyclicH2TorsionInvariantBrauerFreePresentation_inverse_pair K L n e z

end GaloisForLFunctions.HTGeometry.ABHN
