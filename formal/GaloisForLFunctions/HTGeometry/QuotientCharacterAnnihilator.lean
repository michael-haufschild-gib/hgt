import Mathlib.Algebra.Module.CharacterModule

/-!
# Quotient character annihilators

Characters into the rational circle separate points of every abelian group.  Consequently an
additive subgroup is exactly the common annihilator of all characters of its quotient.  This is
the abstract reconstruction step in the holographic Galois correspondence.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A subgroup is the common annihilator of all rational-circle characters of its quotient. -/
theorem mem_addSubgroup_iff_forall_quotientCharacter_eq_zero
    {A : Type*} [AddCommGroup A] (H : AddSubgroup A) (a : A) :
    a ∈ H ↔ ∀ c : CharacterModule (A ⧸ H), c (QuotientAddGroup.mk a) = 0 := by
  constructor
  · intro ha c
    have hzero : (QuotientAddGroup.mk a : A ⧸ H) = 0 :=
      (QuotientAddGroup.eq_zero_iff a).mpr ha
    rw [hzero, map_zero]
  · intro h
    apply (QuotientAddGroup.eq_zero_iff a).mp
    apply CharacterModule.eq_zero_of_character_apply
    exact h

/-- Every shift outside a subgroup is detected by a rational-circle character of the quotient. -/
theorem exists_quotientCharacter_ne_zero_of_not_mem
    {A : Type*} [AddCommGroup A] (H : AddSubgroup A) {a : A} (ha : a ∉ H) :
    ∃ c : CharacterModule (A ⧸ H), c (QuotientAddGroup.mk a) ≠ 0 := by
  apply CharacterModule.exists_character_apply_ne_zero_of_ne_zero
  intro hzero
  exact ha ((QuotientAddGroup.eq_zero_iff a).mp hzero)

end

end GaloisForLFunctions
