import GaloisForLFunctions.RHTower.ChenGuptaLiRamanujanFourier
import GaloisForLFunctions.RHTower.DirichletCompletedLConjugate

/-!
# Chen--Gupta--Li Lemma 6.2: closed primitive functional-equation bridge

Lemma 6.2 reflects the Mellin integral for a character-Poisson transform
through the functional equation of the primitive inducing character.  This
module records that exact algebraic-analytic bridge with all character
conditions carried by a certified packet.  It deliberately does not claim the
lemma's contour shift, truncation, or error estimate; those are separate proof
obligations.
-/

open Complex
open scoped LSeries.notation

noncomputable section

namespace RHTower

/-- A literal positive-modulus primitive nonprincipal character suitable for
the reflection step in CGL Lemma 6.2.  Primitivity and nonprincipality are
certified data; exported theorems expose no raw mathematical premise. -/
structure CGLLemma62PrimitiveCharacter where
  modulus : CGLPositiveModulus
  character : DirichletCharacter ℂ modulus.value
  nonprincipal : character ≠ 1
  primitive : DirichletCharacter.IsPrimitive character

/-- The primitive completed Dirichlet `L` functional equation in the exact
form consumed after the source contour is shifted to the left. -/
theorem cglLemma62_primitiveCompletedL_one_sub
    (P : CGLLemma62PrimitiveCharacter) (s : ℂ) :
    DirichletCharacter.completedLFunction P.character (1 - s) =
      (P.modulus.value : ℂ) ^ (s - 1 / 2) * P.character.rootNumber *
        DirichletCharacter.completedLFunction P.character⁻¹ s := by
  exact P.primitive.completedLFunction_one_sub s

/-- Complex conjugation changes a primitive source character into its inverse
character, exactly as required by the reflected CGL Dirichlet polynomial. -/
theorem cglLemma62_primitiveCompletedL_conj
    (P : CGLLemma62PrimitiveCharacter) (s : ℂ) :
    (starRingEnd ℂ) (DirichletCharacter.completedLFunction P.character s) =
      DirichletCharacter.completedLFunction P.character⁻¹ ((starRingEnd ℂ) s) := by
  exact conj_completedLFunction P.nonprincipal s

/-- Closed completed-`L` reflection in conjugate form.  This combines the
functional equation and the character conjugation identity without adding a
hypothesis on the contour point. -/
theorem cglLemma62_primitiveCompletedL_reflection_conj
    (P : CGLLemma62PrimitiveCharacter) (s : ℂ) :
    DirichletCharacter.completedLFunction P.character (1 - (starRingEnd ℂ) s) =
      (P.modulus.value : ℂ) ^ ((starRingEnd ℂ) s - 1 / 2) * P.character.rootNumber *
        (starRingEnd ℂ) (DirichletCharacter.completedLFunction P.character s) := by
  rw [cglLemma62_primitiveCompletedL_one_sub, cglLemma62_primitiveCompletedL_conj]

/-- The left vertical line used in the first CGL contour shift never meets the
exceptional origin, so its uncompleted `L`-function is exactly the completed
function divided by its Gamma factor. -/
theorem cglLemma62_primitiveLFunction_leftLine_eq_completed_div_gamma
    (P : CGLLemma62PrimitiveCharacter) (v : ℝ) :
    DirichletCharacter.LFunction P.character ((-1 : ℂ) + (v : ℂ) * I) =
      DirichletCharacter.completedLFunction P.character ((-1 : ℂ) + (v : ℂ) * I) /
        P.character.gammaFactor ((-1 : ℂ) + (v : ℂ) * I) := by
  apply DirichletCharacter.LFunction_eq_completed_div_gammaFactor
  left
  intro h
  have hre := congrArg Complex.re h
  simp at hre

/-- The reflected right vertical line has real part two, hence the continued
Dirichlet `L`-function is its absolutely convergent `LSeries`. -/
theorem cglLemma62_inverseLFunction_rightLine_eq_lseries
    (P : CGLLemma62PrimitiveCharacter) (v : ℝ) :
    DirichletCharacter.LFunction P.character⁻¹ ((2 : ℂ) + (v : ℂ) * I) =
      L ↗P.character⁻¹ ((2 : ℂ) + (v : ℂ) * I) := by
  apply DirichletCharacter.LFunction_eq_LSeries
  norm_num

end RHTower
