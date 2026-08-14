import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Coefficientwise Dirichlet-character twists

This file supplies the exact algebraic twist operation needed for Selberg-class factorization.
Twisting is a homomorphism for Dirichlet convolution and composes by multiplication of
characters.  Applying the inverse character does not generally recover the original arithmetic
function: it produces the principal-character depletion, erasing precisely the coefficients whose
indices are not coprime to the modulus.
-/

open Complex

namespace RHTower

noncomputable section

/-- Coefficientwise twist of an arithmetic function by a Dirichlet character. -/
def dirichletCharacterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := χ (n : ZMod q) * f n
  map_zero' := by simp

@[simp]
theorem dirichletCharacterTwist_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) (n : ℕ) :
    dirichletCharacterTwist χ f n = χ (n : ZMod q) * f n := rfl

/-- Retain exactly the coefficients whose indices are coprime to `q`. -/
def characterLevelDepletion (q : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  dirichletCharacterTwist (1 : DirichletCharacter ℂ q) f

/-- Level depletion fixes every coefficient whose index is coprime to the level. -/
theorem characterLevelDepletion_apply_of_coprime {q n : ℕ} (f : ArithmeticFunction ℂ)
    (hn : n.Coprime q) : characterLevelDepletion q f n = f n := by
  rw [characterLevelDepletion, dirichletCharacterTwist_apply,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 hn), one_mul]

/-- Level depletion erases every coefficient whose index is not coprime to the level. -/
theorem characterLevelDepletion_apply_of_not_coprime {q n : ℕ} (f : ArithmeticFunction ℂ)
    (hn : ¬n.Coprime q) : characterLevelDepletion q f n = 0 := by
  rw [characterLevelDepletion, dirichletCharacterTwist_apply,
    MulChar.map_nonunit _ ((ZMod.isUnit_iff_coprime n q).not.mpr hn), zero_mul]

/-- Successive coefficientwise twists multiply their characters. -/
theorem dirichletCharacterTwist_comp {q : ℕ} (ψ χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) :
    dirichletCharacterTwist ψ (dirichletCharacterTwist χ f) =
      dirichletCharacterTwist (ψ * χ) f := by
  ext n
  simp [MulChar.mul_apply, mul_assoc]

/-- Coefficientwise character twist is a homomorphism for Dirichlet convolution. -/
theorem dirichletCharacterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℂ) :
    dirichletCharacterTwist χ (f * g) =
      dirichletCharacterTwist χ f * dirichletCharacterTwist χ g := by
  ext n
  simp only [dirichletCharacterTwist_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  rw [← hprod, Nat.cast_mul, map_mul]
  ring

/-- Inverse twisting is exactly level depletion, not identity in general. -/
theorem dirichletCharacterTwist_inv_twist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) :
    dirichletCharacterTwist χ⁻¹ (dirichletCharacterTwist χ f) =
      characterLevelDepletion q f := by
  rw [dirichletCharacterTwist_comp, MulChar.inv_mul]
  rfl

end


end RHTower
