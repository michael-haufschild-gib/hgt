import GaloisForLFunctions.RHTower.FieldOneGlobalAdeleCharacterQuotient

/-!
# The character quotient of the rational global-adele class group

The additive product formula makes the standard character descend from rational adeles to the
quotient by principal adeles.  The archimedean component realizes every additive-circle value.
Thus, after quotienting the global adele class group by the descended character's kernel, the
remaining obstruction is exactly `ℝ / ℤ`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The global additive character on `𝔸_ℚ / ℚ` is surjective: every circle class is realized at
the archimedean coordinate. -/
theorem fieldOneGlobalAdeleClassCharacter_surjective :
    Function.Surjective fieldOneGlobalAdeleClassCharacter := by
  intro y
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨((fieldOneGlobalAdeleRingEquiv.symm (-r, 0) :
    NumberField.AdeleRing ℤ ℚ) : FieldOneGlobalAdeleAdditiveClassGroup), ?_⟩
  rw [fieldOneGlobalAdeleClassCharacter_mk]
  rw [fieldOneGlobalAdeleStandardUnitAddCircleCharacter]
  change fieldOneSemilocalStandardUnitAddCircleCharacter
    (fieldOneGlobalAdeleRingEquiv (fieldOneGlobalAdeleRingEquiv.symm (-r, 0))) =
      (r : UnitAddCircle)
  rw [fieldOneGlobalAdeleRingEquiv.apply_symm_apply]
  simp [fieldOneSemilocalStandardUnitAddCircleCharacter]

/-- The global class group modulo classes invisible to its additive character is the additive
circle. -/
noncomputable def fieldOneGlobalAdeleClassCharacterQuotientEquiv :
    (FieldOneGlobalAdeleAdditiveClassGroup ⧸ fieldOneGlobalAdeleClassCharacter.ker) ≃+
      UnitAddCircle :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    fieldOneGlobalAdeleClassCharacter fieldOneGlobalAdeleClassCharacter_surjective

/-- The quotient equivalence evaluates a global adele class by its descended character. -/
theorem fieldOneGlobalAdeleClassCharacterQuotientEquiv_mk
    (x : FieldOneGlobalAdeleAdditiveClassGroup) :
    fieldOneGlobalAdeleClassCharacterQuotientEquiv (QuotientAddGroup.mk x) =
      fieldOneGlobalAdeleClassCharacter x := rfl

/-- The character kernel is exactly the image of its inclusion in the global adele class group. -/
theorem fieldOneGlobalAdeleClassCharacter_zeroSum_exact :
    Function.Exact fieldOneGlobalAdeleClassCharacter.ker.subtype
      fieldOneGlobalAdeleClassCharacter := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact y.property

end

end GaloisForLFunctions.RHTower
