/-
# One-prime CRT splitting for bundled quadratic Dirichlet characters

An odd square-free CRT family indexed by `Option I` splits into its head
prime and tail family.  The bundled character is exactly the CRT product of
the corresponding local and tail characters.  This is the induction step for
the composite conductor calculation.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterCoprimePrimitiveProduct
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticCRT
import GaloisForLFunctions.RHTower.DirichletCharacterCRTProduct

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Remove the head of an `Option`-indexed certified prime family. -/
def optionTail (P : OddPrimeFamily (Option I)) : OddPrimeFamily I where
  prime i := P.prime (some i)
  pairwise_ne i j hij := P.pairwise_ne (by simpa using hij)

/-- The `Option`-indexed modulus is literally its head prime times its tail modulus. -/
theorem option_modulus (P : OddPrimeFamily (Option I)) :
    P.modulus = (P.prime none).1 * P.optionTail.modulus := by
  simp [modulus, optionTail]

/-- The head prime is coprime to the product of the tail primes. -/
theorem option_head_coprime_tail (P : OddPrimeFamily (Option I)) :
    Nat.Coprime (P.prime none).1 P.optionTail.modulus := by
  rw [optionTail, modulus]
  apply Nat.Coprime.prod_right
  intro i hi
  exact P.pairwise_coprime (by simp)

/-- CRT equivalence grouping the head coordinate and all tail coordinates. -/
def optionCrtProductEquiv (P : OddPrimeFamily (Option I)) :
    ZMod P.modulus ≃+* (ZMod (P.prime none).1 × ZMod P.optionTail.modulus) :=
  P.crtEquiv.trans (RingEquiv.piOptionEquivProd.trans
    (RingEquiv.prodCongr (RingEquiv.refl _) P.optionTail.crtEquiv.symm))

/-- Product of the head prime-field quadratic character and the tail CRT character. -/
def optionCanonicalCharacter (P : OddPrimeFamily (Option I)) :
    DirichletCharacter ℂ P.modulus :=
  crtProductCharacter P.optionCrtProductEquiv (oddPrimeQuadraticCharacter (P.prime none))
    (quadraticDirichletCharacter P.optionTail)

/-- First coordinate of the grouped CRT equivalence. -/
theorem optionCrtProductEquiv_fst (P : OddPrimeFamily (Option I)) (x : ZMod P.modulus) :
    (P.optionCrtProductEquiv x).1 = P.crtEquiv x none := by
  rfl

/-- The tail CRT coordinates recover the remaining coordinates of the full CRT equivalence. -/
theorem optionCrtProductEquiv_tail (P : OddPrimeFamily (Option I)) (x : ZMod P.modulus)
    (i : I) :
    P.optionTail.crtEquiv (P.optionCrtProductEquiv x).2 i = P.crtEquiv x (some i) := by
  change P.optionTail.crtEquiv
      (P.optionTail.crtEquiv.symm (fun j => P.crtEquiv x (some j))) i = _
  rw [RingEquiv.apply_symm_apply]

/-- The bundled character of an `Option`-indexed family is exactly its head/tail CRT product. -/
theorem quadraticDirichletCharacter_option_eq_canonical (P : OddPrimeFamily (Option I)) :
    quadraticDirichletCharacter P = P.optionCanonicalCharacter := by
  classical
  apply MulChar.ext'
  intro x
  rw [quadraticDirichletCharacter_apply, quadraticCharacter,
    oddPrimeFamilyQuadraticCharacter, optionCanonicalCharacter,
    crtProductCharacter_apply, quadraticDirichletCharacter_apply, quadraticCharacter,
    oddPrimeFamilyQuadraticCharacter]
  rw [optionCrtProductEquiv_fst]
  simp_rw [optionCrtProductEquiv_tail]
  change (∏ i, (oddPrimeQuadraticCharacter (P.prime i)) (P.crtEquiv x i)) = _
  rw [Fintype.prod_option]
  change
    (oddPrimeQuadraticCharacter (P.prime none)) (P.crtEquiv x none) *
        ∏ i, (oddPrimeQuadraticCharacter (P.prime (some i))) (P.crtEquiv x (some i)) =
      (oddPrimeQuadraticCharacter (P.prime none)) (P.crtEquiv x none) *
        ∏ i, (oddPrimeQuadraticCharacter (P.prime (some i))) (P.crtEquiv x (some i))
  rfl

/-- The head prime divides the modulus of an `Option`-indexed family. -/
theorem option_head_dvd_modulus (P : OddPrimeFamily (Option I)) :
    (P.prime none).1 ∣ P.modulus := by
  rw [option_modulus]
  exact dvd_mul_right (P.prime none).1 P.optionTail.modulus

/-- The tail modulus divides the modulus of an `Option`-indexed family. -/
theorem option_tail_dvd_modulus (P : OddPrimeFamily (Option I)) :
    P.optionTail.modulus ∣ P.modulus := by
  rw [option_modulus]
  exact P.optionTail.modulus.dvd_mul_left (P.prime none).1

/-- Literal product of the head and tail characters lifted to the full modulus. -/
def optionLiftedCharacter (P : OddPrimeFamily (Option I)) :
    DirichletCharacter ℂ P.modulus :=
  DirichletCharacter.changeLevel (option_head_dvd_modulus P)
    (oddPrimeQuadraticCharacter (P.prime none)) *
  DirichletCharacter.changeLevel (option_tail_dvd_modulus P)
    (quadraticDirichletCharacter P.optionTail)

/-- The CRT split character is exactly the literal product of its head and tail lifts. -/
theorem optionCanonicalCharacter_eq_lifted (P : OddPrimeFamily (Option I)) :
    P.optionCanonicalCharacter = P.optionLiftedCharacter := by
  apply MulChar.ext'
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  by_cases hz : IsCoprime z (P.modulus : ℤ)
  · have hcoord : P.optionCrtProductEquiv (z : ZMod P.modulus) =
        ((z : ZMod (P.prime none).1), (z : ZMod P.optionTail.modulus)) := by
      exact map_intCast P.optionCrtProductEquiv z
    rw [optionCanonicalCharacter, crtProductCharacter_apply, hcoord,
      optionLiftedCharacter, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd'
        (oddPrimeQuadraticCharacter (P.prime none)) (option_head_dvd_modulus P) hz,
      DirichletCharacter.changeLevel_eq_cast_of_dvd'
        (quadraticDirichletCharacter P.optionTail) (option_tail_dvd_modulus P) hz]
  · have hnonunit : ¬ IsUnit ((z : ℤ) : ZMod P.modulus) := by
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      exact fun h => hz h.symm
    rw [optionCanonicalCharacter, MulChar.map_nonunit _ hnonunit,
      optionLiftedCharacter, MulChar.map_nonunit _ hnonunit]

end OddPrimeFamily
end RHTower
