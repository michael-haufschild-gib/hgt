/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerPresentation

/-!
# First isomorphism theorem for the cyclic H² Brauer presentation

The free additive group on cyclic degree-two cohomology classes maps onto the cyclic relative
Brauer subgroup.  Quotienting by the exact relation subgroup therefore gives an additive
isomorphism to that subgroup.  This is an unconditional additive replacement for the still
missing tensor-product formula: that formula would identify the quotient directly with `H²`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

/-- The cyclic relative Brauer subgroup is the free additive cyclic `H²` presentation modulo
its exact relation subgroup. -/
noncomputable def cyclicGaloisH2BrauerPresentationQuotientAddEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    FreeAbelianGroup (cyclicGaloisH2 K L) ⧸ cyclicGaloisH2BrauerRelationSubgroup K L ≃+
      cyclicGaloisBrauerSubgroup K L :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (cyclicGaloisH2BrauerFreePresentation K L)
    (cyclicGaloisH2BrauerFreePresentation_surjective K L)

/-- On a quotient representative, the presentation isomorphism is the original free
presentation. -/
theorem cyclicGaloisH2BrauerPresentationQuotientAddEquiv_mk
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (w : FreeAbelianGroup (cyclicGaloisH2 K L)) :
    cyclicGaloisH2BrauerPresentationQuotientAddEquiv K L (QuotientAddGroup.mk w) =
      cyclicGaloisH2BrauerFreePresentation K L w := rfl

/-- The induced additive map from the exact cyclic `H²` quotient to the ambient Brauer group. -/
noncomputable def cyclicGaloisH2BrauerPresentationQuotientAddHom
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    FreeAbelianGroup (cyclicGaloisH2 K L) ⧸ cyclicGaloisH2BrauerRelationSubgroup K L →+
      BrauerGroup K :=
  (cyclicGaloisBrauerSubgroup K L).subtype.comp
    (cyclicGaloisH2BrauerPresentationQuotientAddEquiv K L).toAddMonoidHom

/-- A quotient generator maps to its selected cyclic `H²` Brauer representative. -/
theorem cyclicGaloisH2BrauerPresentationQuotientAddHom_apply_mk_of
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2BrauerPresentationQuotientAddHom K L
      (QuotientAddGroup.mk (FreeAbelianGroup.of z)) = cyclicGaloisH2BrauerMap K L z := by
  change ((cyclicGaloisH2BrauerPresentationQuotientAddEquiv K L
    (QuotientAddGroup.mk (FreeAbelianGroup.of z)) : cyclicGaloisBrauerSubgroup K L) :
      BrauerGroup K) = cyclicGaloisH2BrauerMap K L z
  rw [cyclicGaloisH2BrauerPresentationQuotientAddEquiv_mk,
    cyclicGaloisH2BrauerFreePresentation_apply_of_coe]

end GaloisForLFunctions.HTGeometry.ABHN
