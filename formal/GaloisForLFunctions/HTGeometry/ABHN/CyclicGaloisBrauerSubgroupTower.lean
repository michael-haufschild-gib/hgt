/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerInflation
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerFaithful

/-!
# Cyclic Brauer subgroups in finite Galois towers

In a finite cyclic Galois tower, every Brauer class represented at a lower field layer is also
represented at the upper layer. The subgroup inclusion commutes exactly with the oriented cyclic
`H²` transition. This is the source-side directedness theorem needed to assemble local invariants
once a cofinal tower of unramified extensions has been constructed.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Cyclic Brauer subgroups are monotone along finite cyclic Galois field towers. -/
theorem cyclicGaloisBrauerSubgroup_le_of_isScalarTower
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    cyclicGaloisBrauerSubgroup K L ≤ cyclicGaloisBrauerSubgroup K M := by
  intro x hx
  obtain ⟨z, hz⟩ :=
    cyclicGaloisH2BrauerSubgroupAddHom_surjective K L ⟨x, hx⟩
  have hzval : cyclicGaloisH2BrauerMap K L z = x := congrArg Subtype.val hz
  have hmem := cyclicGaloisH2BrauerMap_mem_cyclicGaloisBrauerSubgroup K M
    (cyclicGaloisH2OrientedNormQuotientTransition K L M z)
  rwa [cyclicGaloisH2BrauerMap_orientedNormQuotientTransition K L M z, hzval] at hmem

/-- Additive inclusion of a lower cyclic Brauer subgroup into the subgroup of an upper tower
layer. -/
noncomputable def cyclicGaloisBrauerSubgroupTowerInclusion
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    cyclicGaloisBrauerSubgroup K L →+ cyclicGaloisBrauerSubgroup K M :=
  AddSubgroup.inclusion (cyclicGaloisBrauerSubgroup_le_of_isScalarTower K L M)

/-- Under the cyclic `H²` descriptions, Brauer-subgroup inclusion is the oriented norm-quotient
transition. -/
theorem cyclicGaloisBrauerSubgroupTowerInclusion_h2
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (z : cyclicGaloisH2 K L) :
    cyclicGaloisBrauerSubgroupTowerInclusion K L M
        (cyclicGaloisH2BrauerSubgroupAddEquiv K L z) =
      cyclicGaloisH2BrauerSubgroupAddEquiv K M
        (cyclicGaloisH2OrientedNormQuotientTransition K L M z) := by
  apply Subtype.ext
  exact (cyclicGaloisH2BrauerMap_orientedNormQuotientTransition K L M z).symm

end

end GaloisForLFunctions.HTGeometry.ABHN
