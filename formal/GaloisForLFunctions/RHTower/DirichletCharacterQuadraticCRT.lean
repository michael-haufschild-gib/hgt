/-
# Bundled odd square-free CRT quadratic Dirichlet characters

The existing Jacobi-sum layer defines the certified odd square-free quadratic
character as a function on `ZMod q`.  This module proves that exact function
is a `DirichletCharacter`: its unit restriction is the finite product of the
already bundled prime-field quadratic characters, and it is extended by zero
on nonunits.  No multiplicativity or conductor premise is introduced.
-/
import GaloisForLFunctions.RHTower.QuadraticJacobiSum
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.NumberTheory.DirichletCharacter.Basic

open scoped BigOperators

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- The `i`th prime-field unit coordinate induced by the certified CRT equivalence. -/
def crtUnitCoordinate (P : OddPrimeFamily I) (i : I) :
    (ZMod P.modulus)ˣ →* (ZMod (P.prime i).1)ˣ :=
  Units.map ((Pi.evalMonoidHom (fun i => ZMod (P.prime i).1) i).comp
    P.crtEquiv.toMonoidHom)

/-- Product on the unit group of all certified prime-field quadratic characters. -/
def quadraticUnitHom (P : OddPrimeFamily I) : (ZMod P.modulus)ˣ →* ℂˣ where
  toFun u := ∏ i, (oddPrimeQuadraticCharacter (P.prime i)).toUnitHom (crtUnitCoordinate P i u)
  map_one' := by
    simp [crtUnitCoordinate]
  map_mul' u v := by
    simp only [crtUnitCoordinate, map_mul, Finset.prod_mul_distrib]

/-- The bundled Dirichlet character associated to the certified odd square-free CRT family. -/
def quadraticDirichletCharacter (P : OddPrimeFamily I) : DirichletCharacter ℂ P.modulus :=
  MulChar.ofUnitHom (quadraticUnitHom P)

/-- The bundled character is exactly the pre-existing CRT quadratic-character function. -/
theorem quadraticDirichletCharacter_apply (P : OddPrimeFamily I) (x : ZMod P.modulus) :
    quadraticDirichletCharacter P x = quadraticCharacter P x := by
  classical
  by_cases hx : IsUnit x
  · rcases hx with ⟨u, rfl⟩
    simp [quadraticDirichletCharacter, quadraticUnitHom, quadraticCharacter,
      oddPrimeFamilyQuadraticCharacter, crtUnitCoordinate]
  · rw [MulChar.map_nonunit _ hx]
    rw [quadraticCharacter, oddPrimeFamilyQuadraticCharacter]
    have hpi : ¬ IsUnit (P.crtEquiv x) := by
      intro h
      exact hx (by simpa using (h.map P.crtEquiv.symm.toMonoidHom))
    rw [Pi.isUnit_iff] at hpi
    obtain ⟨i, hi⟩ := not_forall.mp hpi
    symm
    exact Finset.prod_eq_zero (f := fun j =>
      oddPrimeQuadraticCharacter (P.prime j) (P.crtEquiv x j))
      (Finset.mem_univ i) (MulChar.map_nonunit _ hi)

/-- The bundled odd square-free CRT character is quadratic. -/
theorem oddPrimeQuadraticCharacter_isQuadratic (p : OddPrime) :
    (oddPrimeQuadraticCharacter p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p.1)).comp (Int.castRingHom ℂ)

/-- Finite products of the certified prime-field quadratic characters remain quadratic. -/
theorem quadraticDirichletCharacter_isQuadratic (P : OddPrimeFamily I) :
    (quadraticDirichletCharacter P).IsQuadratic := by
  classical
  intro x
  rw [quadraticDirichletCharacter_apply, quadraticCharacter,
    oddPrimeFamilyQuadraticCharacter]
  have hprod (s : Finset I) :
      (∏ i ∈ s, oddPrimeQuadraticCharacter (P.prime i) (P.crtEquiv x i)) = 0 ∨
        (∏ i ∈ s, oddPrimeQuadraticCharacter (P.prime i) (P.crtEquiv x i)) = 1 ∨
        (∏ i ∈ s, oddPrimeQuadraticCharacter (P.prime i) (P.crtEquiv x i)) = -1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rcases oddPrimeQuadraticCharacter_isQuadratic (P.prime i) (P.crtEquiv x i)
        with hzero | hone | hneg <;>
        rcases ih with hzero' | hone' | hneg' <;>
          simp_all [Finset.prod_insert]
  simpa using hprod Finset.univ

end OddPrimeFamily
end RHTower
