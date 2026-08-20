/-
# Conductor certificates for two-adic/odd CRT quadratic characters

This module identifies the bundled CRT characters at levels `4q` and `8q`
with the corresponding products of lifted local characters.  It proves their
full primitivity and conductor identities.  The remaining source-facing work
is fundamental-discriminant classification and exact local correlation bounds.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterCoprimePrimitiveProduct
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicCRTProduct
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicPrimitive
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticCRTPrimitive

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- The level-four factor divides the literal CRT modulus. -/
theorem four_dvd_fourOddModulus (P : OddPrimeFamily I) : 4 ∣ fourOddModulus P := by
  rw [fourOddModulus_eq]
  exact dvd_mul_right 4 P.modulus

/-- The odd factor divides the literal level-four CRT modulus. -/
theorem odd_dvd_fourOddModulus (P : OddPrimeFamily I) : P.modulus ∣ fourOddModulus P := by
  rw [fourOddModulus_eq]
  exact P.modulus.dvd_mul_left 4

/-- Product of the lifted level-four and certified odd quadratic characters. -/
def fourOddCanonicalCharacter (P : OddPrimeFamily I) :
    DirichletCharacter ℂ (fourOddModulus P) :=
  DirichletCharacter.changeLevel (four_dvd_fourOddModulus P) quadraticCharacterFour *
  DirichletCharacter.changeLevel (odd_dvd_fourOddModulus P) (quadraticDirichletCharacter P)

/-- The CRT-bundled level-four character is exactly its lifted local product. -/
theorem fourOddQuadraticDirichletCharacter_eq_canonical (P : OddPrimeFamily I) :
    fourOddQuadraticDirichletCharacter P = fourOddCanonicalCharacter P := by
  apply MulChar.ext'
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  by_cases hz : IsCoprime z (fourOddModulus P : ℤ)
  · rw [fourOddQuadraticDirichletCharacter_apply, fourOddQuadraticCharacter,
      fourCoordinate_intCast, oddCoordinate_intCast, fourOddCanonicalCharacter,
      MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' quadraticCharacterFour
        (four_dvd_fourOddModulus P) hz,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadraticDirichletCharacter P)
        (odd_dvd_fourOddModulus P) hz,
      quadraticDirichletCharacter_apply]
  · have hnonunit : ¬ IsUnit ((z : ℤ) : ZMod (fourOddModulus P)) := by
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      exact fun h => hz h.symm
    rw [MulChar.map_nonunit _ hnonunit, MulChar.map_nonunit _ hnonunit]

/-- The conductor of the bundled level-four CRT character retains its full
two-adic factor. -/
theorem four_dvd_fourOddQuadraticDirichletCharacter_conductor (P : OddPrimeFamily I) :
    4 ∣ (fourOddQuadraticDirichletCharacter P).conductor := by
  rw [fourOddQuadraticDirichletCharacter_eq_canonical]
  exact lifted_coprime_product_left_conductor_dvd_at_level quadraticCharacterFour
    (quadraticDirichletCharacter P) (four_coprime_modulus P)
    quadraticCharacterFour_isPrimitive (four_dvd_fourOddModulus P)
    (odd_dvd_fourOddModulus P)

/-- The bundled level-four/odd CRT quadratic character is primitive at its full modulus. -/
theorem fourOddQuadraticDirichletCharacter_isPrimitive (P : OddPrimeFamily I) :
    (fourOddQuadraticDirichletCharacter P).IsPrimitive := by
  rw [fourOddQuadraticDirichletCharacter_eq_canonical]
  exact lifted_coprime_product_isPrimitive_at_level quadraticCharacterFour
    (quadraticDirichletCharacter P) (four_coprime_modulus P)
    quadraticCharacterFour_isPrimitive (quadraticDirichletCharacter_isPrimitive P)
    (four_dvd_fourOddModulus P) (odd_dvd_fourOddModulus P)
    (fourOddModulus_eq P)

/-- The level-eight factor divides the literal CRT modulus. -/
theorem eight_dvd_eightOddModulus (P : OddPrimeFamily I) : 8 ∣ eightOddModulus P := by
  rw [eightOddModulus_eq]
  exact dvd_mul_right 8 P.modulus

/-- The odd factor divides the literal level-eight CRT modulus. -/
theorem odd_dvd_eightOddModulus (P : OddPrimeFamily I) : P.modulus ∣ eightOddModulus P := by
  rw [eightOddModulus_eq]
  exact P.modulus.dvd_mul_left 8

/-- Product of the lifted first level-eight and certified odd quadratic characters. -/
def eightOddCanonicalCharacterEight (P : OddPrimeFamily I) :
    DirichletCharacter ℂ (eightOddModulus P) :=
  DirichletCharacter.changeLevel (eight_dvd_eightOddModulus P) quadraticCharacterEight *
  DirichletCharacter.changeLevel (odd_dvd_eightOddModulus P) (quadraticDirichletCharacter P)

/-- The first CRT-bundled level-eight character is its lifted local product. -/
theorem eightOddQuadraticDirichletCharacterEight_eq_canonical (P : OddPrimeFamily I) :
    eightOddQuadraticDirichletCharacterEight P = eightOddCanonicalCharacterEight P := by
  apply MulChar.ext'
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  by_cases hz : IsCoprime z (eightOddModulus P : ℤ)
  · rw [eightOddQuadraticDirichletCharacterEight_apply,
      eightOddQuadraticCharacterEight, eightOddQuadraticCharacter,
      eightCoordinate_intCast, eightOddCoordinate_intCast, eightOddCanonicalCharacterEight,
      MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' quadraticCharacterEight
        (eight_dvd_eightOddModulus P) hz,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadraticDirichletCharacter P)
        (odd_dvd_eightOddModulus P) hz,
      quadraticDirichletCharacter_apply]
  · have hnonunit : ¬ IsUnit ((z : ℤ) : ZMod (eightOddModulus P)) := by
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      exact fun h => hz h.symm
    rw [MulChar.map_nonunit _ hnonunit, MulChar.map_nonunit _ hnonunit]

/-- The first bundled level-eight CRT character retains its full two-adic
factor in its conductor. -/
theorem eight_dvd_eightOddQuadraticDirichletCharacterEight_conductor
    (P : OddPrimeFamily I) :
    8 ∣ (eightOddQuadraticDirichletCharacterEight P).conductor := by
  rw [eightOddQuadraticDirichletCharacterEight_eq_canonical]
  exact lifted_coprime_product_left_conductor_dvd_at_level quadraticCharacterEight
    (quadraticDirichletCharacter P) (eight_coprime_modulus P)
    quadraticCharacterEight_isPrimitive (eight_dvd_eightOddModulus P)
    (odd_dvd_eightOddModulus P)

/-- The first bundled level-eight/odd CRT quadratic character is primitive at its full modulus. -/
theorem eightOddQuadraticDirichletCharacterEight_isPrimitive (P : OddPrimeFamily I) :
    (eightOddQuadraticDirichletCharacterEight P).IsPrimitive := by
  rw [eightOddQuadraticDirichletCharacterEight_eq_canonical]
  exact lifted_coprime_product_isPrimitive_at_level quadraticCharacterEight
    (quadraticDirichletCharacter P) (eight_coprime_modulus P)
    quadraticCharacterEight_isPrimitive (quadraticDirichletCharacter_isPrimitive P)
    (eight_dvd_eightOddModulus P) (odd_dvd_eightOddModulus P)
    (eightOddModulus_eq P)

/-- Product of the lifted second level-eight and certified odd quadratic characters. -/
def eightOddCanonicalCharacterEightPrime (P : OddPrimeFamily I) :
    DirichletCharacter ℂ (eightOddModulus P) :=
  DirichletCharacter.changeLevel (eight_dvd_eightOddModulus P) quadraticCharacterEightPrime *
  DirichletCharacter.changeLevel (odd_dvd_eightOddModulus P) (quadraticDirichletCharacter P)

/-- The second CRT-bundled level-eight character is its lifted local product. -/
theorem eightOddQuadraticDirichletCharacterEightPrime_eq_canonical (P : OddPrimeFamily I) :
    eightOddQuadraticDirichletCharacterEightPrime P =
      eightOddCanonicalCharacterEightPrime P := by
  apply MulChar.ext'
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  by_cases hz : IsCoprime z (eightOddModulus P : ℤ)
  · rw [eightOddQuadraticDirichletCharacterEightPrime_apply,
      eightOddQuadraticCharacterEightPrime, eightOddQuadraticCharacter,
      eightCoordinate_intCast, eightOddCoordinate_intCast,
      eightOddCanonicalCharacterEightPrime, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' quadraticCharacterEightPrime
        (eight_dvd_eightOddModulus P) hz,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadraticDirichletCharacter P)
        (odd_dvd_eightOddModulus P) hz,
      quadraticDirichletCharacter_apply]
  · have hnonunit : ¬ IsUnit ((z : ℤ) : ZMod (eightOddModulus P)) := by
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      exact fun h => hz h.symm
    rw [MulChar.map_nonunit _ hnonunit, MulChar.map_nonunit _ hnonunit]

/-- The second bundled level-eight CRT character retains its full two-adic
factor in its conductor. -/
theorem eight_dvd_eightOddQuadraticDirichletCharacterEightPrime_conductor
    (P : OddPrimeFamily I) :
    8 ∣ (eightOddQuadraticDirichletCharacterEightPrime P).conductor := by
  rw [eightOddQuadraticDirichletCharacterEightPrime_eq_canonical]
  exact lifted_coprime_product_left_conductor_dvd_at_level quadraticCharacterEightPrime
    (quadraticDirichletCharacter P) (eight_coprime_modulus P)
    quadraticCharacterEightPrime_isPrimitive (eight_dvd_eightOddModulus P)
    (odd_dvd_eightOddModulus P)

/-- The second bundled level-eight/odd CRT quadratic character is primitive at its full modulus. -/
theorem eightOddQuadraticDirichletCharacterEightPrime_isPrimitive (P : OddPrimeFamily I) :
    (eightOddQuadraticDirichletCharacterEightPrime P).IsPrimitive := by
  rw [eightOddQuadraticDirichletCharacterEightPrime_eq_canonical]
  exact lifted_coprime_product_isPrimitive_at_level quadraticCharacterEightPrime
    (quadraticDirichletCharacter P) (eight_coprime_modulus P)
    quadraticCharacterEightPrime_isPrimitive (quadraticDirichletCharacter_isPrimitive P)
    (eight_dvd_eightOddModulus P) (odd_dvd_eightOddModulus P)
    (eightOddModulus_eq P)

end OddPrimeFamily
end RHTower
