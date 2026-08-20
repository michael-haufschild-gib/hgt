import GaloisForLFunctions.RHTower.FieldOneGlobalAdeleComparison

/-!
# The global adelic additive character on the principal quotient

The product formula says that the standard additive character of the rational
adele ring vanishes on every principal rational adele.  This file records its
universal algebraic consequence: the character descends to the additive
quotient `𝔸_ℚ / ℚ`, and remains nonzero there.

This is the additive quotient occurring in global harmonic analysis.  It is a
genuine product-formula / global-reciprocity consequence, rather than a
substitute for the still-unformalized Brauer-group ABHN sequence.  No topology
on the quotient or Pontryagin-duality theorem is asserted here.
-/

namespace GaloisForLFunctions.RHTower

open NumberField

noncomputable section

/-- Principal rational adeles, regarded as an additive subgroup of the global
rational adele ring. -/
noncomputable def fieldOnePrincipalAdeleAddSubgroup :
    AddSubgroup (NumberField.AdeleRing ℤ ℚ) :=
  AddSubgroup.map
    (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)).toAddMonoidHom ⊤

/-- The additive quotient of rational adeles by their principal rational
subgroup. -/
abbrev FieldOneGlobalAdeleAdditiveClassGroup :=
  NumberField.AdeleRing ℤ ℚ ⧸ fieldOnePrincipalAdeleAddSubgroup

/-- The standard global additive character descends to the principal-adele
quotient. -/
noncomputable def fieldOneGlobalAdeleClassCharacter :
    FieldOneGlobalAdeleAdditiveClassGroup →+ UnitAddCircle :=
  QuotientAddGroup.lift fieldOnePrincipalAdeleAddSubgroup
    fieldOneGlobalAdeleStandardUnitAddCircleCharacter (by
      intro x hx
      rcases hx with ⟨q, -, rfl⟩
      exact fieldOneGlobalAdeleStandardUnitAddCircleCharacter_principal q)

/-- The descended character agrees with the standard character on an adele
representative. -/
theorem fieldOneGlobalAdeleClassCharacter_mk
    (x : NumberField.AdeleRing ℤ ℚ) :
    fieldOneGlobalAdeleClassCharacter
        (x : FieldOneGlobalAdeleAdditiveClassGroup) =
      fieldOneGlobalAdeleStandardUnitAddCircleCharacter x :=
  QuotientAddGroup.lift_mk _ _ x

/-- The product formula is precisely the assertion that each principal
rational adele is killed before passing to the quotient. -/
theorem fieldOneGlobalAdeleClassCharacter_principal
    (q : ℚ) :
    fieldOneGlobalAdeleClassCharacter
        ((algebraMap ℚ (NumberField.AdeleRing ℤ ℚ) q :
          NumberField.AdeleRing ℤ ℚ) : FieldOneGlobalAdeleAdditiveClassGroup) = 0 := by
  rw [fieldOneGlobalAdeleClassCharacter_mk]
  exact fieldOneGlobalAdeleStandardUnitAddCircleCharacter_principal q

/-- The descended global character is nonzero, so global reciprocity does not
collapse the additive adele quotient. -/
theorem fieldOneGlobalAdeleClassCharacter_ne_zero :
    fieldOneGlobalAdeleClassCharacter ≠ 0 := by
  intro h
  apply fieldOneGlobalAdeleStandardUnitAddCircleCharacter_ne_zero
  ext x
  have hx := DFunLike.congr_fun h
    (x : FieldOneGlobalAdeleAdditiveClassGroup)
  rw [fieldOneGlobalAdeleClassCharacter_mk] at hx
  simpa using hx

end

end GaloisForLFunctions.RHTower
