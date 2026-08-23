/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerSubgroup

/-!
# Additive presentation of the cyclic relative Brauer layer

For a fixed finite cyclic Galois extension `L/K`, selected cyclic `H²` representatives generate
the additive subgroup of `Br(K)` split by `L`.  The selected representative map is not yet known
to be additive: that is exactly the missing tensor-product comparison for cyclic algebras.

This file records the resulting honest additive object.  The free abelian group on selected `H²`
classes maps surjectively to the cyclic relative Brauer subgroup.  Its kernel is the precise
additive relation object to which the future tensor formula must contribute.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- The additive presentation sending a formal selected cyclic `H²` representative to its cyclic
Brauer class. -/
noncomputable def cyclicGaloisH2BrauerFreePresentation
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    FreeAbelianGroup (cyclicGaloisH2 K L) →+ cyclicGaloisBrauerSubgroup K L :=
  FreeAbelianGroup.lift (cyclicGaloisH2BrauerSubgroupMap K L)

/-- The relation subgroup in the additive presentation of the cyclic relative Brauer layer. -/
noncomputable def cyclicGaloisH2BrauerRelationSubgroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    AddSubgroup (FreeAbelianGroup (cyclicGaloisH2 K L)) :=
  (cyclicGaloisH2BrauerFreePresentation K L).ker

/-- A free generator maps to its selected cyclic `H²` Brauer representative. -/
theorem cyclicGaloisH2BrauerFreePresentation_apply_of
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2BrauerFreePresentation K L (FreeAbelianGroup.of z) =
      cyclicGaloisH2BrauerSubgroupMap K L z := by
  change FreeAbelianGroup.lift (cyclicGaloisH2BrauerSubgroupMap K L)
    (FreeAbelianGroup.of z) = cyclicGaloisH2BrauerSubgroupMap K L z
  exact FreeAbelianGroup.lift_apply_of (cyclicGaloisH2BrauerSubgroupMap K L) z

/-- On ambient Brauer classes, a free generator maps to the selected cyclic `H²` class. -/
theorem cyclicGaloisH2BrauerFreePresentation_apply_of_coe
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (z : cyclicGaloisH2 K L) :
    ((cyclicGaloisH2BrauerFreePresentation K L (FreeAbelianGroup.of z) :
      cyclicGaloisBrauerSubgroup K L) : BrauerGroup K) =
      cyclicGaloisH2BrauerMap K L z := by
  rw [cyclicGaloisH2BrauerFreePresentation_apply_of,
    cyclicGaloisH2BrauerSubgroupMap_coe]

/-- After inclusion in `Br(K)`, the presentation is the free additive extension of the selected
cyclic `H²` Brauer map. -/
theorem cyclicGaloisH2BrauerFreePresentation_comp_subtype
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    (cyclicGaloisBrauerSubgroup K L).subtype.comp
      (cyclicGaloisH2BrauerFreePresentation K L) =
      FreeAbelianGroup.lift (cyclicGaloisH2BrauerMap K L) := by
  apply FreeAbelianGroup.lift_ext
  intro z
  simp only [AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of,
    AddSubgroup.subtype_apply]
  exact cyclicGaloisH2BrauerFreePresentation_apply_of_coe K L z

/-- The presentation followed by the relative Brauer-kernel map is the free additive extension
of the selected relative cyclic `H²` map. -/
theorem cyclicGaloisH2BrauerFreePresentation_comp_toRelativeBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) :
    (cyclicGaloisBrauerSubgroupToRelativeBrauerKernel K L).comp
      (cyclicGaloisH2BrauerFreePresentation K L) =
      FreeAbelianGroup.lift (cyclicGaloisH2RelativeBrauerMap K L n hdeg) := by
  apply FreeAbelianGroup.lift_ext
  intro z
  simp only [AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of]
  rw [cyclicGaloisH2BrauerFreePresentation_apply_of]
  exact cyclicGaloisH2BrauerSubgroupMap_toRelativeBrauerKernel_eq K L n hdeg z

/-- Selected cyclic `H²` representatives give a surjective additive presentation of the cyclic
relative Brauer subgroup. -/
theorem cyclicGaloisH2BrauerFreePresentation_surjective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    Function.Surjective (cyclicGaloisH2BrauerFreePresentation K L) := by
  intro x
  have hx : (x : BrauerGroup K) ∈
      AddSubgroup.closure (Set.range (cyclicGaloisH2BrauerMap K L)) := by
    rw [← cyclicGaloisBrauerSubgroup_eq_closure_range_cyclicGaloisH2BrauerMap]
    exact x.property
  have hle : AddSubgroup.closure (Set.range (cyclicGaloisH2BrauerMap K L)) ≤
      ((cyclicGaloisBrauerSubgroup K L).subtype.comp
        (cyclicGaloisH2BrauerFreePresentation K L)).range := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨z, rfl⟩
    refine ⟨FreeAbelianGroup.of z, ?_⟩
    exact cyclicGaloisH2BrauerFreePresentation_apply_of_coe K L z
  rcases hle hx with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact hw

end GaloisForLFunctions.HTGeometry.ABHN
