/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerInverse
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerPresentation

/-!
# Inverse relations in the cyclic `H²` Brauer presentation

The free additive presentation of the relative cyclic Brauer layer records all relations between
selected `H²` representatives.  Brauer inversion forces one explicit family: the formal pair
`z + (-z)` is in its relation subgroup.  This is an unconditional part of the future
tensor-product relation, which would identify the entire presentation quotient directly with
`H²`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Opposite cyclic `H²` classes cancel under the free presentation into the relative Brauer
subgroup. -/
theorem cyclicGaloisH2BrauerFreePresentation_inverse_pair
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2BrauerFreePresentation K L
      (FreeAbelianGroup.of z + FreeAbelianGroup.of (-z)) = 0 := by
  rw [map_add, cyclicGaloisH2BrauerFreePresentation_apply_of,
    cyclicGaloisH2BrauerFreePresentation_apply_of]
  apply Subtype.ext
  change cyclicGaloisH2BrauerMap K L z + cyclicGaloisH2BrauerMap K L (-z) = brauerSplitClass K
  rw [← cyclicGaloisH2BrauerMap_brauerTensorNeg K L z]
  exact add_neg_cancel _

/-- The formal inverse pair belongs to the exact relation subgroup of the cyclic `H²` Brauer
presentation. -/
theorem cyclicGaloisH2Brauer_inverse_pair_mem_relation
    (z : cyclicGaloisH2 K L) :
    FreeAbelianGroup.of z + FreeAbelianGroup.of (-z) ∈
      cyclicGaloisH2BrauerRelationSubgroup K L := by
  exact cyclicGaloisH2BrauerFreePresentation_inverse_pair K L z

end GaloisForLFunctions.HTGeometry.ABHN
