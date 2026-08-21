import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveReduction

noncomputable section

namespace RHTower

/-- The conductor of a certified nonprincipal character, represented as a literal divisor of its
original modulus.  This is the finite divisor datum used when an all-character estimate is
assembled from primitive estimates at every divisor. -/
noncomputable def cglPrimitiveConductorDivisor
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) : (n + 1).divisors :=
  ⟨χ.1.conductor, (Nat.mem_divisors.mpr
    ⟨(cglPrimitiveCharacterReduction n χ).conductor_dvd_modulus, Nat.succ_ne_zero n⟩)⟩

/-- The value of the closed divisor datum is exactly the standard conductor. -/
theorem cglPrimitiveConductorDivisor_val_eq_conductor
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    (cglPrimitiveConductorDivisor n χ).1 = χ.1.conductor :=
  rfl

/-- The primitive source character expressed at the literal conductor divisor. -/
noncomputable def cglPrimitiveCharacterAtConductorDivisor
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter ℂ (cglPrimitiveConductorDivisor n χ).1 :=
  (cglPrimitiveCharacterReduction n χ).primitiveCharacter

/-- The primitive source character at the literal conductor divisor is primitive. -/
theorem cglPrimitiveCharacterAtConductorDivisor_primitive
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter.IsPrimitive (cglPrimitiveCharacterAtConductorDivisor n χ) :=
  cglPrimitiveCharacterReduction_primitive n χ

/-- The primitive source character at the literal conductor divisor is nonprincipal. -/
theorem cglPrimitiveCharacterAtConductorDivisor_nonprincipal
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    cglPrimitiveCharacterAtConductorDivisor n χ ≠ 1 :=
  cglPrimitiveCharacterReduction_nonprincipal n χ

end RHTower
