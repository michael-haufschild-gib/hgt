import GaloisForLFunctions.RHTower.FieldOneGlobalAdeleCharacterKernelQuotient

/-!
# Hasse classification for the full rational global-adele character

Two rational global-adele classes have equal descended additive character exactly when they differ
by a character-neutral class.  Every additive-circle value has a representative unique modulo that
kernel.
-/

namespace GaloisForLFunctions.RHTower

/-- Equality of global adelic characters is congruence modulo the character kernel. -/
theorem fieldOneGlobalAdeleClassCharacter_congr_hasse_iff
    (x y : FieldOneGlobalAdeleAdditiveClassGroup) :
    x - y ∈ fieldOneGlobalAdeleClassCharacter.ker ↔
      fieldOneGlobalAdeleClassCharacter x = fieldOneGlobalAdeleClassCharacter y := by
  change fieldOneGlobalAdeleClassCharacter (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every additive-circle value has a rational global-adele class representative, unique modulo
character-neutral classes. -/
theorem fieldOneGlobalAdeleClassCharacter_exists_unique_mod_zeroSum
    (z : UnitAddCircle) :
    ∃ x : FieldOneGlobalAdeleAdditiveClassGroup,
      fieldOneGlobalAdeleClassCharacter x = z ∧
      ∀ y : FieldOneGlobalAdeleAdditiveClassGroup,
        fieldOneGlobalAdeleClassCharacter y = z ↔
          y - x ∈ fieldOneGlobalAdeleClassCharacter.ker := by
  obtain ⟨x, hx⟩ := fieldOneGlobalAdeleClassCharacter_surjective z
  refine ⟨x, hx, fun y => ?_⟩
  rw [← hx]
  exact (fieldOneGlobalAdeleClassCharacter_congr_hasse_iff y x).symm

end GaloisForLFunctions.RHTower
