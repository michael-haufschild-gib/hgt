/-
# Primitivity of bundled odd square-free CRT quadratic characters

This module turns the exact head/tail CRT split into the induction step for
the conductor of the bundled odd square-free quadratic character.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticCRTSplit

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- If the tail bundled character is primitive, then adjoining a new distinct
odd-prime quadratic factor gives a primitive bundled character. -/
theorem quadraticDirichletCharacter_option_isPrimitive_of_tail
    (P : OddPrimeFamily (Option I))
    (hTail : (quadraticDirichletCharacter P.optionTail).IsPrimitive) :
    (quadraticDirichletCharacter P).IsPrimitive := by
  rw [quadraticDirichletCharacter_option_eq_canonical,
    optionCanonicalCharacter_eq_lifted]
  exact lifted_coprime_product_isPrimitive_at_level
    (oddPrimeQuadraticCharacter (P.prime none))
    (quadraticDirichletCharacter P.optionTail)
    (option_head_coprime_tail P)
    (oddPrimeQuadraticCharacter_isPrimitive (P.prime none))
    hTail
    (option_head_dvd_modulus P)
    (option_tail_dvd_modulus P)
    (option_modulus P)

/-- The bundled character of the empty prime family is the level-one trivial character. -/
theorem quadraticDirichletCharacter_empty_isPrimitive
    (P : OddPrimeFamily (PEmpty : Type u_1)) :
    (quadraticDirichletCharacter P).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hmod : P.modulus = 1 := by simp [modulus]
  have hchar : quadraticDirichletCharacter P = 1 := by
    apply MulChar.ext'
    intro x
    by_cases hx : IsUnit x
    · rcases hx with ⟨u, rfl⟩
      simp [quadraticDirichletCharacter, quadraticUnitHom]
    · rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit _ hx]
  calc
    (quadraticDirichletCharacter P).conductor = 1 :=
      DirichletCharacter.eq_one_iff_conductor_eq_one.mp hchar
    _ = P.modulus := hmod.symm

/-- Reindex a certified odd-prime family along a finite equivalence. -/
def reindex {J : Type*} [Fintype J] (P : OddPrimeFamily I) (e : J ≃ I) :
    OddPrimeFamily J where
  prime j := P.prime (e j)
  pairwise_ne _ _ hjk := P.pairwise_ne (e.injective.ne hjk)

/-- Reindexing preserves the literal product modulus. -/
theorem reindex_modulus {J : Type*} [Fintype J] (P : OddPrimeFamily I) (e : J ≃ I) :
    (P.reindex e).modulus = P.modulus := by
  exact Fintype.prod_equiv e (fun j => ((P.reindex e).prime j).1)
    (fun i => (P.prime i).1) (by intro j; rfl)

/-- The reindexed modulus divides the original equal modulus. -/
theorem reindex_modulus_dvd {J : Type*} [Fintype J] (P : OddPrimeFamily I) (e : J ≃ I) :
    (P.reindex e).modulus ∣ P.modulus := by
  rw [reindex_modulus]

/-- After lifting to the equal modulus, reindexing leaves the bundled character unchanged. -/
theorem reindex_changeLevel_eq {J : Type*} [Fintype J] (P : OddPrimeFamily I) (e : J ≃ I) :
    DirichletCharacter.changeLevel (reindex_modulus_dvd P e)
      (quadraticDirichletCharacter (P.reindex e)) = quadraticDirichletCharacter P := by
  apply MulChar.ext'
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  by_cases hz : IsCoprime z (P.modulus : ℤ)
  · have hz' : IsCoprime z ((P.reindex e).modulus : ℤ) := by
      rw [reindex_modulus]
      exact hz
    have hP : P.crtEquiv (z : ZMod P.modulus) = fun i => (z : ZMod (P.prime i).1) := by
      exact map_intCast P.crtEquiv z
    have hQ : (P.reindex e).crtEquiv (z : ZMod (P.reindex e).modulus) =
        fun j => (z : ZMod ((P.reindex e).prime j).1) := by
      exact map_intCast (P.reindex e).crtEquiv z
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd'
        (quadraticDirichletCharacter (P.reindex e)) (reindex_modulus_dvd P e) hz,
      quadraticDirichletCharacter_apply, quadraticCharacter,
      oddPrimeFamilyQuadraticCharacter, hQ,
      quadraticDirichletCharacter_apply, quadraticCharacter,
      oddPrimeFamilyQuadraticCharacter, hP]
    exact Fintype.prod_equiv e
      (fun j => oddPrimeQuadraticCharacter ((P.reindex e).prime j)
        (z : ZMod ((P.reindex e).prime j).1))
      (fun i => oddPrimeQuadraticCharacter (P.prime i) (z : ZMod (P.prime i).1))
      (by intro j; rfl)
  · have hnonunit : ¬ IsUnit ((z : ℤ) : ZMod P.modulus) := by
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      exact fun h => hz h.symm
    rw [MulChar.map_nonunit _ hnonunit, MulChar.map_nonunit _ hnonunit]

/-- Primitivity transports back from a reindexed finite prime family. -/
theorem reindex_isPrimitive_of_isPrimitive {J : Type*} [Fintype J]
    (P : OddPrimeFamily I) (e : J ≃ I)
    (hQ : (quadraticDirichletCharacter (P.reindex e)).IsPrimitive) :
    (quadraticDirichletCharacter P).IsPrimitive := by
  rw [← reindex_changeLevel_eq P e]
  rw [DirichletCharacter.isPrimitive_def]
  rw [DirichletCharacter.conductor_changeLevel]
  calc
    (quadraticDirichletCharacter (P.reindex e)).conductor = (P.reindex e).modulus := hQ
    _ = P.modulus := reindex_modulus P e

/-- Every certified finite odd square-free CRT quadratic character is primitive. -/
theorem quadraticDirichletCharacter_isPrimitive (P : OddPrimeFamily I) :
    (quadraticDirichletCharacter P).IsPrimitive := by
  let Q : ∀ (α : Type u_1) [Fintype α], Prop := fun α _ =>
    ∀ P : OddPrimeFamily α, (quadraticDirichletCharacter P).IsPrimitive
  apply Fintype.induction_empty_option (P := Q)
  · intro α β hβ e h P
    letI : Fintype α := Fintype.ofEquiv β e.symm
    exact reindex_isPrimitive_of_isPrimitive P e (h (P.reindex e))
  · intro P
    exact quadraticDirichletCharacter_empty_isPrimitive P
  · intro α _ h P
    exact quadraticDirichletCharacter_option_isPrimitive_of_tail P (h P.optionTail)

end OddPrimeFamily
end RHTower
