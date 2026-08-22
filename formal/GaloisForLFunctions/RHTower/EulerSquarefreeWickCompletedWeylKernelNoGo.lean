import GaloisForLFunctions.RHTower.EulerSquarefreeWickRegularOrbitFlux

/-!
# Completed Weyl-kernel obstruction for the Euler--Wick regular orbit

The completed regular orbit has four Fourier sectors: Xi and the completed mod-3, mod-4, and
mod-12 quadratic L-functions.  It is tempting to use the two residue gauges as a Pauli/Weyl action
on the kernel at a Xi zero and then import Kramers or Clifford multiplicity.

This file gives the exact test.  In Fourier coordinates the completed carrier is diagonal, while
the two Weyl shifts tensor a character label with the mod-3 or mod-4 character.  Their orbit of the
vacuum is the entire four-sector basis.  Consequently, that orbit lies in the completed kernel iff
all four completed functions vanish at the same point.  A Xi zero alone supplies only the vacuum
kernel line; the character shifts move it into auxiliary L-sectors rather than preserving it.

Thus the full Pauli/Clifford transplant does not manufacture the missing orientation law.  The
positive survivor is precise: a viable EWQ action must be a non-unitary incidence or boundary
operation that returns to the Xi sector without requiring auxiliary common zeros.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Coordinatewise action of a four-sector Fourier multiplier. -/
def quadraticResidueFourierDiagonalAction
    (A v : QuadraticResidueFourierCoordinates ℂ) :
    QuadraticResidueFourierCoordinates ℂ where
  vacuum := A.vacuum * v.vacuum
  fst := A.fst * v.fst
  snd := A.snd * v.snd
  joint := A.joint * v.joint

/-- Zero vector in the four quadratic Fourier sectors. -/
def quadraticResidueFourierZero : QuadraticResidueFourierCoordinates ℂ where
  vacuum := 0
  fst := 0
  snd := 0
  joint := 0

/-- Vacuum-character basis vector. -/
def quadraticResidueVacuumBasis : QuadraticResidueFourierCoordinates ℂ where
  vacuum := 1
  fst := 0
  snd := 0
  joint := 0

/-- First Weyl shift: tensor the Fourier label with the mod-3 character. -/
def quadraticResidueFstWeylShift
    (v : QuadraticResidueFourierCoordinates ℂ) :
    QuadraticResidueFourierCoordinates ℂ where
  vacuum := v.fst
  fst := v.vacuum
  snd := v.joint
  joint := v.snd

/-- Second Weyl shift: tensor the Fourier label with the mod-4 character. -/
def quadraticResidueSndWeylShift
    (v : QuadraticResidueFourierCoordinates ℂ) :
    QuadraticResidueFourierCoordinates ℂ where
  vacuum := v.snd
  fst := v.joint
  snd := v.vacuum
  joint := v.fst

/-- The four completed function values, before taking logarithmic derivatives. -/
def eulerSquarefreeWickCompletedValueCoordinates (s : ℂ) :
    QuadraticResidueFourierCoordinates ℂ where
  vacuum := _root_.RHTower.xi s
  fst := DirichletCharacter.completedLFunction quadraticCharacterThree s
  snd := DirichletCharacter.completedLFunction RHTower.quadraticCharacterFour s
  joint := DirichletCharacter.completedLFunction quadraticCharacterTwelve s

/-- The rank-two Weyl orbit of the vacuum is killed by the completed diagonal precisely when all
four completed Fourier sectors vanish together.  This is the exact common-zero obstruction to
using the literal EWQ residue translations as Clifford symmetries of a Xi divisor kernel. -/
theorem eulerSquarefreeWick_completed_fullWeylOrbit_killed_iff (s : ℂ) :
    let A := eulerSquarefreeWickCompletedValueCoordinates s
    let e := quadraticResidueVacuumBasis
    quadraticResidueFourierDiagonalAction A e = quadraticResidueFourierZero ∧
      quadraticResidueFourierDiagonalAction A (quadraticResidueFstWeylShift e) =
        quadraticResidueFourierZero ∧
      quadraticResidueFourierDiagonalAction A (quadraticResidueSndWeylShift e) =
        quadraticResidueFourierZero ∧
      quadraticResidueFourierDiagonalAction A
          (quadraticResidueFstWeylShift (quadraticResidueSndWeylShift e)) =
        quadraticResidueFourierZero ↔
      _root_.RHTower.xi s = 0 ∧
        DirichletCharacter.completedLFunction quadraticCharacterThree s = 0 ∧
        DirichletCharacter.completedLFunction RHTower.quadraticCharacterFour s = 0 ∧
        DirichletCharacter.completedLFunction quadraticCharacterTwelve s = 0 := by
  simp [eulerSquarefreeWickCompletedValueCoordinates,
    quadraticResidueFourierDiagonalAction, quadraticResidueFourierZero,
    quadraticResidueVacuumBasis, quadraticResidueFstWeylShift,
    quadraticResidueSndWeylShift, QuadraticResidueFourierCoordinates.ext_iff]

end

end GaloisForLFunctions.RHTower
