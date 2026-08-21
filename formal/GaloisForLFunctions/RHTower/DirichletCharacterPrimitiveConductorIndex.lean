import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveReduction

noncomputable section

namespace RHTower

/-- The conductor minus one of a certified nonprincipal character modulo `n + 1` lies in the
finite conductor-index range through `n`. -/
theorem cglPrimitiveCharacterReduction_conductor_sub_one_le_modulus_index
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    χ.1.conductor - 1 ≤ n := by
  have hpos : 0 < χ.1.conductor :=
    (cglPrimitiveCharacterReduction n χ).conductor_pos
  have hdvd : χ.1.conductor ∣ n + 1 :=
    (cglPrimitiveCharacterReduction n χ).conductor_dvd_modulus
  have hle : χ.1.conductor ≤ n + 1 :=
    Nat.le_of_dvd (Nat.succ_pos n) hdvd
  omega

/-- The closed finite conductor index of the primitive source of a nonprincipal character.
The value `d - 1` represents its positive conductor `d` in the range `0, …, n`. -/
noncomputable def cglPrimitiveConductorIndex
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) : Fin (n + 1) :=
  ⟨χ.1.conductor - 1,
    Nat.lt_succ_of_le (cglPrimitiveCharacterReduction_conductor_sub_one_le_modulus_index n χ)⟩

/-- Recover the positive conductor from its closed finite source index. -/
theorem cglPrimitiveConductorIndex_succ_eq_conductor
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    (cglPrimitiveConductorIndex n χ).1 + 1 = χ.1.conductor := by
  change χ.1.conductor - 1 + 1 = χ.1.conductor
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (DirichletCharacter.conductor_ne_zero χ.1))

/-- The primitive source character expressed at its finite conductor index. -/
noncomputable def cglPrimitiveCharacterAtConductorIndex
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter ℂ ((cglPrimitiveConductorIndex n χ).1 + 1) :=
  (cglPrimitiveConductorIndex_succ_eq_conductor n χ).symm ▸
    (cglPrimitiveCharacterReduction n χ).primitiveCharacter

/-- The primitive source character at the closed conductor index is primitive. -/
theorem cglPrimitiveCharacterAtConductorIndex_primitive
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter.IsPrimitive (cglPrimitiveCharacterAtConductorIndex n χ) := by
  have transportPrimitive : ∀ {a b : ℕ} (h : a = b)
      (ψ : DirichletCharacter ℂ a), DirichletCharacter.IsPrimitive ψ →
      DirichletCharacter.IsPrimitive (h ▸ ψ) := by
    intro a b h ψ hprimitive
    cases h
    exact hprimitive
  unfold cglPrimitiveCharacterAtConductorIndex
  exact transportPrimitive (cglPrimitiveConductorIndex_succ_eq_conductor n χ).symm
    (cglPrimitiveCharacterReduction n χ).primitiveCharacter
    (cglPrimitiveCharacterReduction_primitive n χ)

/-- The primitive source character at the closed conductor index is nonprincipal. -/
theorem cglPrimitiveCharacterAtConductorIndex_nonprincipal
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    cglPrimitiveCharacterAtConductorIndex n χ ≠ 1 := by
  have transportNonprincipal : ∀ {a b : ℕ} (h : a = b)
      (ψ : DirichletCharacter ℂ a), ψ ≠ 1 → (h ▸ ψ) ≠ 1 := by
    intro a b h ψ hnonprincipal
    cases h
    exact hnonprincipal
  unfold cglPrimitiveCharacterAtConductorIndex
  exact transportNonprincipal (cglPrimitiveConductorIndex_succ_eq_conductor n χ).symm
    (cglPrimitiveCharacterReduction n χ).primitiveCharacter
    (cglPrimitiveCharacterReduction_nonprincipal n χ)

end RHTower
