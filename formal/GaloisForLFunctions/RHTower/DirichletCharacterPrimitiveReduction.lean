import GaloisForLFunctions.RHTower.DirichletLZeroCount

noncomputable section

namespace RHTower

/-- Closed primitive-conductor reduction for a certified nonprincipal Dirichlet character.

The record packages the algebraic part of reduction to a primitive character: the conductor is
positive and divides the original modulus, its primitive character is nonprincipal, and changing
level back to the original modulus recovers the input character exactly.  This makes no analytic
claim about the relation between the associated Dirichlet `L`-functions or their zeros. -/
structure CGLPrimitiveCharacterReduction
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) where
  conductor : ℕ
  conductor_pos : 0 < conductor
  conductor_dvd_modulus : conductor ∣ n + 1
  primitiveCharacter : DirichletCharacter ℂ conductor
  primitive : DirichletCharacter.IsPrimitive primitiveCharacter
  nonprincipal : primitiveCharacter ≠ 1
  induced_eq : DirichletCharacter.changeLevel conductor_dvd_modulus primitiveCharacter = χ.1

/-- Every certified nonprincipal character is induced from its nonprincipal primitive character
at its conductor. -/
noncomputable def cglPrimitiveCharacterReduction
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    CGLPrimitiveCharacterReduction n χ where
  conductor := χ.1.conductor
  conductor_pos := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ.1)
  conductor_dvd_modulus := χ.1.conductor_dvd_level
  primitiveCharacter := χ.1.primitiveCharacter
  primitive := χ.1.primitiveCharacter_isPrimitive
  nonprincipal := by
    intro h
    have hind := χ.1.changeLevel_primitiveCharacter
    rw [h, DirichletCharacter.changeLevel_one] at hind
    exact χ.2 hind.symm
  induced_eq := χ.1.changeLevel_primitiveCharacter

/-- The conductor in the closed primitive reduction is the standard conductor of the input. -/
theorem cglPrimitiveCharacterReduction_conductor_eq
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    (cglPrimitiveCharacterReduction n χ).conductor = χ.1.conductor :=
  rfl

/-- The character packaged by the closed reduction is primitive. -/
theorem cglPrimitiveCharacterReduction_primitive
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter.IsPrimitive (cglPrimitiveCharacterReduction n χ).primitiveCharacter :=
  (cglPrimitiveCharacterReduction n χ).primitive

/-- The primitive character packaged by the closed reduction is nonprincipal. -/
theorem cglPrimitiveCharacterReduction_nonprincipal
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    (cglPrimitiveCharacterReduction n χ).primitiveCharacter ≠ 1 :=
  (cglPrimitiveCharacterReduction n χ).nonprincipal

/-- Changing level from the conductor in the closed reduction recovers the input character. -/
theorem cglPrimitiveCharacterReduction_induced_eq
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter.changeLevel
      (cglPrimitiveCharacterReduction n χ).conductor_dvd_modulus
      (cglPrimitiveCharacterReduction n χ).primitiveCharacter = χ.1 :=
  (cglPrimitiveCharacterReduction n χ).induced_eq

end RHTower
