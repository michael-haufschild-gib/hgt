import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveReduction

noncomputable section

namespace RHTower

/-- An integer equipped with its coprimality certificate for the literal modulus `n + 1`.
The certificate is data, so character-agreement theorems have no unresolved premise. -/
structure CGLCoprimeModulusInteger (n : ℕ) where
  value : ℤ
  coprime : IsCoprime value (n + 1 : ℕ)

/-- A natural coefficient index equipped with its coprimality certificate for the literal modulus
`n + 1`. -/
structure CGLCoprimeModulusNatural (n : ℕ) where
  value : ℕ
  coprime : value.Coprime (n + 1)

/-- View a certified natural coefficient index as a certified integer index. -/
def CGLCoprimeModulusNatural.toInteger
    {n : ℕ} (a : CGLCoprimeModulusNatural n) : CGLCoprimeModulusInteger n :=
  ⟨a.value, Nat.isCoprime_iff_coprime.mpr a.coprime⟩

/-- At every integer coprime to the original modulus, a certified nonprincipal character agrees
exactly with its canonical primitive conductor character. -/
theorem cglPrimitiveCharacterReduction_apply_of_coprime
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    (a : CGLCoprimeModulusInteger n) :
    χ.1 a.value = (cglPrimitiveCharacterReduction n χ).primitiveCharacter a.value := by
  rw [← (cglPrimitiveCharacterReduction n χ).induced_eq]
  exact DirichletCharacter.changeLevel_eq_cast_of_dvd'
    (cglPrimitiveCharacterReduction n χ).primitiveCharacter
    (cglPrimitiveCharacterReduction n χ).conductor_dvd_modulus a.coprime

/-- Natural-index form of primitive-character agreement at every coefficient coprime to the
original modulus. -/
theorem cglPrimitiveCharacterReduction_apply_nat_of_coprime
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    (a : CGLCoprimeModulusNatural n) :
    χ.1 a.value = (cglPrimitiveCharacterReduction n χ).primitiveCharacter a.value := by
  simpa [CGLCoprimeModulusNatural.toInteger, Int.cast_natCast] using
    cglPrimitiveCharacterReduction_apply_of_coprime n χ a.toInteger

end RHTower
