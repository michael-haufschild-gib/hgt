import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveAgreement

noncomputable section

namespace RHTower

/-- Exact coefficientwise level depletion for a nonprincipal character and its primitive
conductor source.  At indices coprime to the original modulus the two characters agree; every
other coefficient of the imprimitive character vanishes.  This is the finite Euler-deletion
identity before any assertion about infinite Euler products or zero divisors. -/
theorem cglPrimitiveCharacterReduction_apply_eq_levelDepletion
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (m : ℕ) :
    χ.1 m = if m.Coprime (n + 1) then
      (cglPrimitiveCharacterReduction n χ).primitiveCharacter m else 0 := by
  by_cases hcop : m.Coprime (n + 1)
  · rw [if_pos hcop]
    exact cglPrimitiveCharacterReduction_apply_nat_of_coprime n χ ⟨m, hcop⟩
  · rw [if_neg hcop]
    rw [χ.1.map_nonunit]
    rwa [ZMod.isUnit_iff_coprime]

end RHTower
