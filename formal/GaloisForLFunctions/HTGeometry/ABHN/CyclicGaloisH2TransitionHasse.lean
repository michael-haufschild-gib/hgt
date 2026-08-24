import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisRestrictionOrientation

/-!
# Hasse quotients for oriented cyclic Galois H² transitions

Generator-oriented norm-quotient transition is treated as a local comparison place. Quotienting by
classes it kills gives exactly its realized upper-level range. Through a tower, invisibility is
monotone: a class killed at an intermediate level remains killed at every higher level.
-/

open CategoryTheory Representation

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
  [IsGalois K L] [IsGalois K M]
  [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]

/-- Lower cyclic `H²` classes modulo those invisible after oriented transition to `M`. -/
abbrev CyclicGaloisH2OrientedTransitionHasseClass :=
  cyclicGaloisH2 K L ⧸
    (cyclicGaloisH2OrientedNormQuotientTransition K L M).ker

/-- First-isomorphism classification by upper classes actually realized. -/
noncomputable def cyclicGaloisH2OrientedTransitionHasseEquivRange :
    CyclicGaloisH2OrientedTransitionHasseClass K L M ≃+
      (cyclicGaloisH2OrientedNormQuotientTransition K L M).range :=
  QuotientAddGroup.quotientKerEquivRange _

@[simp] theorem cyclicGaloisH2OrientedTransitionHasseEquivRange_mk
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2OrientedTransitionHasseEquivRange K L M
        (QuotientAddGroup.mk z) =
      ⟨cyclicGaloisH2OrientedNormQuotientTransition K L M z, ⟨z, rfl⟩⟩ := by
  rfl

/-- Two lower classes have same upper transition exactly when their difference is invisible. -/
theorem cyclicGaloisH2OrientedTransition_congr_hasse_iff
    (z w : cyclicGaloisH2 K L) :
    z - w ∈ (cyclicGaloisH2OrientedNormQuotientTransition K L M).ker ↔
      cyclicGaloisH2OrientedNormQuotientTransition K L M z =
        cyclicGaloisH2OrientedNormQuotientTransition K L M w := by
  change cyclicGaloisH2OrientedNormQuotientTransition K L M (z - w) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- A transition quotient class vanishes exactly when its oriented upper class vanishes. -/
theorem cyclicGaloisH2OrientedTransitionClass_eq_zero_hasse_iff
    (z : cyclicGaloisH2 K L) :
    (QuotientAddGroup.mk z : CyclicGaloisH2OrientedTransitionHasseClass K L M) = 0 ↔
      cyclicGaloisH2OrientedNormQuotientTransition K L M z = 0 := by
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- Nonzero surviving class is witnessed by a nonzero oriented upper transition. -/
theorem cyclicGaloisH2OrientedTransitionClass_ne_zero_hasse_iff
    (z : cyclicGaloisH2 K L) :
    (QuotientAddGroup.mk z : CyclicGaloisH2OrientedTransitionHasseClass K L M) ≠ 0 ↔
      cyclicGaloisH2OrientedNormQuotientTransition K L M z ≠ 0 := by
  exact not_congr (cyclicGaloisH2OrientedTransitionClass_eq_zero_hasse_iff K L M z)

/-- Identity-tower Hasse quotient has no invisible nonzero classes. -/
theorem cyclicGaloisH2OrientedTransition_self_ker
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    (cyclicGaloisH2OrientedNormQuotientTransition K L L).ker = ⊥ := by
  rw [cyclicGaloisH2OrientedNormQuotientTransition_self]
  ext z
  simp

/-- Once a cyclic `H²` class is invisible at an intermediate level, it remains invisible above it. -/
theorem cyclicGaloisH2OrientedTransition_ker_mono
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)] :
    (cyclicGaloisH2OrientedNormQuotientTransition K L M).ker ≤
      (cyclicGaloisH2OrientedNormQuotientTransition K L N).ker := by
  intro z hz
  change cyclicGaloisH2OrientedNormQuotientTransition K L N z = 0
  rw [← cyclicGaloisH2OrientedNormQuotientTransition_comp K L M N,
    AddMonoidHom.comp_apply]
  change cyclicGaloisH2OrientedNormQuotientTransition K L M z = 0 at hz
  rw [hz, map_zero]

/-- Survival at an upper level forces survival at every intermediate level. -/
theorem cyclicGaloisH2OrientedTransition_survival_anti
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)]
    (z : cyclicGaloisH2 K L)
    (h : cyclicGaloisH2OrientedNormQuotientTransition K L N z ≠ 0) :
    cyclicGaloisH2OrientedNormQuotientTransition K L M z ≠ 0 := by
  intro hz
  exact h (cyclicGaloisH2OrientedTransition_ker_mono K L M N
    (show z ∈ (cyclicGaloisH2OrientedNormQuotientTransition K L M).ker from hz))

end

end GaloisForLFunctions.HTGeometry.ABHN
