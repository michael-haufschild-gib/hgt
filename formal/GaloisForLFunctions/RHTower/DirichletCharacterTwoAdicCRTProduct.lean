/-
# Bundled two-adic/odd CRT quadratic Dirichlet characters

The finite-correlation and second-moment layers already use three explicit CRT
quadratic value functions at moduli `4q` and `8q`. This module proves each is
the evaluation of a bundled complex Dirichlet character, with no change to
those established value-level results.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterCRTProduct
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticCRT
import GaloisForLFunctions.RHTower.DirichletCharacterEightOddCRT
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicCRT

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Bundled level-four times odd CRT quadratic character. -/
def fourOddQuadraticDirichletCharacter (P : OddPrimeFamily I) :
    DirichletCharacter ℂ (fourOddModulus P) :=
  crtProductCharacter (fourOddCrtProductEquiv P) quadraticCharacterFour
    (quadraticDirichletCharacter P)

/-- The bundled level-four CRT character is exactly the established value function. -/
theorem fourOddQuadraticDirichletCharacter_apply (P : OddPrimeFamily I)
    (x : ZMod (fourOddModulus P)) :
    fourOddQuadraticDirichletCharacter P x = fourOddQuadraticCharacter P x := by
  rw [fourOddQuadraticDirichletCharacter, crtProductCharacter_apply,
    quadraticDirichletCharacter_apply]
  rfl

/-- Bundled first level-eight times odd CRT quadratic character. -/
def eightOddQuadraticDirichletCharacterEight (P : OddPrimeFamily I) :
    DirichletCharacter ℂ (eightOddModulus P) :=
  crtProductCharacter (eightOddCrtProductEquiv P) quadraticCharacterEight
    (quadraticDirichletCharacter P)

/-- The first bundled level-eight CRT character is exactly the established value function. -/
theorem eightOddQuadraticDirichletCharacterEight_apply (P : OddPrimeFamily I)
    (x : ZMod (eightOddModulus P)) :
    eightOddQuadraticDirichletCharacterEight P x = eightOddQuadraticCharacterEight P x := by
  rw [eightOddQuadraticDirichletCharacterEight, crtProductCharacter_apply,
    quadraticDirichletCharacter_apply]
  rfl

/-- Bundled second level-eight times odd CRT quadratic character. -/
def eightOddQuadraticDirichletCharacterEightPrime (P : OddPrimeFamily I) :
    DirichletCharacter ℂ (eightOddModulus P) :=
  crtProductCharacter (eightOddCrtProductEquiv P) quadraticCharacterEightPrime
    (quadraticDirichletCharacter P)

/-- The second bundled level-eight CRT character is exactly the established value function. -/
theorem eightOddQuadraticDirichletCharacterEightPrime_apply (P : OddPrimeFamily I)
    (x : ZMod (eightOddModulus P)) :
    eightOddQuadraticDirichletCharacterEightPrime P x =
      eightOddQuadraticCharacterEightPrime P x := by
  rw [eightOddQuadraticDirichletCharacterEightPrime, crtProductCharacter_apply,
    quadraticDirichletCharacter_apply]
  rfl

/-- The bundled level-four/odd CRT character is quadratic. -/
theorem fourOddQuadraticDirichletCharacter_isQuadratic (P : OddPrimeFamily I) :
    (fourOddQuadraticDirichletCharacter P).IsQuadratic :=
  crtProductCharacter_isQuadratic (fourOddCrtProductEquiv P) quadraticCharacterFour
    (quadraticDirichletCharacter P) quadraticCharacterFour_isQuadratic
    (quadraticDirichletCharacter_isQuadratic P)

/-- The bundled first level-eight/odd CRT character is quadratic. -/
theorem eightOddQuadraticDirichletCharacterEight_isQuadratic (P : OddPrimeFamily I) :
    (eightOddQuadraticDirichletCharacterEight P).IsQuadratic :=
  crtProductCharacter_isQuadratic (eightOddCrtProductEquiv P) quadraticCharacterEight
    (quadraticDirichletCharacter P) quadraticCharacterEight_isQuadratic
    (quadraticDirichletCharacter_isQuadratic P)

/-- The bundled second level-eight/odd CRT character is quadratic. -/
theorem eightOddQuadraticDirichletCharacterEightPrime_isQuadratic (P : OddPrimeFamily I) :
    (eightOddQuadraticDirichletCharacterEightPrime P).IsQuadratic :=
  crtProductCharacter_isQuadratic (eightOddCrtProductEquiv P) quadraticCharacterEightPrime
    (quadraticDirichletCharacter P) quadraticCharacterEightPrime_isQuadratic
    (quadraticDirichletCharacter_isQuadratic P)

end OddPrimeFamily
end RHTower
