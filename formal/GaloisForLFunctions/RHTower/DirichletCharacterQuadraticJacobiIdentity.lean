/-
# Jacobi identities for the bundled square-free quadratic characters

This module identifies the concrete odd square-free CRT Dirichlet character
with Mathlib's Jacobi symbol at every integer input.  It is the odd part of
the source-facing fundamental-discriminant character identification.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticCRTPrimitive
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

noncomputable section

namespace RHTower
namespace OddPrimeFamily

/-- The prime-field quadratic character is the Jacobi symbol at its prime modulus. -/
theorem oddPrimeQuadraticCharacter_intCast_eq_jacobi (p : OddPrime) (n : ℤ) :
    oddPrimeQuadraticCharacter p (n : ZMod p.1) = (jacobiSym n p.1 : ℂ) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym p.1 n]
  rfl

/-- The bundled square-free CRT quadratic character is the Jacobi symbol of its modulus. -/
theorem quadraticDirichletCharacter_intCast_eq_jacobi {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) (n : ℤ) :
    quadraticDirichletCharacter P (n : ZMod P.modulus) = (jacobiSym n P.modulus : ℂ) := by
  let Q : ∀ (α : Type u_1) [Fintype α], Prop := fun α _ =>
    ∀ (P : OddPrimeFamily α) (n : ℤ),
      quadraticDirichletCharacter P (n : ZMod P.modulus) = (jacobiSym n P.modulus : ℂ)
  apply Fintype.induction_empty_option (P := Q)
  · intro α β hβ e h P n
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have hvalue : quadraticDirichletCharacter P (n : ZMod P.modulus) =
        quadraticDirichletCharacter (P.reindex e)
          (n : ZMod (P.reindex e).modulus) := by
      rw [quadraticDirichletCharacter_apply, quadraticCharacter,
        oddPrimeFamilyQuadraticCharacter, quadraticDirichletCharacter_apply,
        quadraticCharacter, oddPrimeFamilyQuadraticCharacter]
      have hP : P.crtEquiv (n : ZMod P.modulus) =
          fun i => (n : ZMod (P.prime i).1) := by
        exact map_intCast P.crtEquiv n
      have hQ : (P.reindex e).crtEquiv (n : ZMod (P.reindex e).modulus) =
          fun j => (n : ZMod ((P.reindex e).prime j).1) := by
        exact map_intCast (P.reindex e).crtEquiv n
      rw [hP, hQ]
      exact (Fintype.prod_equiv e
        (fun j => oddPrimeQuadraticCharacter ((P.reindex e).prime j)
          (n : ZMod ((P.reindex e).prime j).1))
        (fun i => oddPrimeQuadraticCharacter (P.prime i) (n : ZMod (P.prime i).1))
        (by intro j; rfl)).symm
    calc
      quadraticDirichletCharacter P (n : ZMod P.modulus) =
          quadraticDirichletCharacter (P.reindex e)
            (n : ZMod (P.reindex e).modulus) := hvalue
      _ = (jacobiSym n (P.reindex e).modulus : ℂ) := h (P.reindex e) n
      _ = (jacobiSym n P.modulus : ℂ) := by rw [P.reindex_modulus e]
  · intro P n
    rw [quadraticDirichletCharacter_apply, quadraticCharacter,
      oddPrimeFamilyQuadraticCharacter]
    simp [modulus]
  · intro α _ h P n
    rw [quadraticDirichletCharacter_option_eq_canonical, optionCanonicalCharacter,
      crtProductCharacter_apply]
    have hcoord : P.optionCrtProductEquiv (n : ZMod P.modulus) =
        ((n : ZMod (P.prime none).1), (n : ZMod P.optionTail.modulus)) := by
      exact map_intCast P.optionCrtProductEquiv n
    rw [hcoord, oddPrimeQuadraticCharacter_intCast_eq_jacobi, h P.optionTail n]
    have hJ : (jacobiSym n ((P.prime none).1 * P.optionTail.modulus) : ℂ) =
        (jacobiSym n (P.prime none).1 : ℂ) * (jacobiSym n P.optionTail.modulus : ℂ) := by
      norm_cast
      exact jacobiSym.mul_right n (P.prime none).1 P.optionTail.modulus
    rw [← hJ, P.option_modulus]

end OddPrimeFamily
end RHTower
