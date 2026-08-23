/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.PrimeCyclicGeneratorHasse
import GaloisForLFunctions.RHTower.PrimeTorsionAutonomousCircuitPolygon

/-!
# Hasse detection on prime-torsion phase polygons

The unit additive circle contains a canonical copy of every prime cyclic phase group.  Restricting
an additive observable to that polygon is completely controlled by the primitive phase.  Thus the
restriction is either zero or faithful, with no intermediate prime-order collapse.
-/

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Canonical additive phase chart for a prime cyclic group, with primality supplying nonzero
modulus internally. -/
def primeZmodUnitAddCirclePhaseHom (p : Nat.Primes) : ZMod p →+ UnitAddCircle := by
  letI : NeZero p.1 := ⟨p.2.ne_zero⟩
  exact zmodUnitAddCirclePhaseHom p

/-- The canonical prime-torsion phase chart is faithful. -/
theorem primeZmodUnitAddCirclePhaseHom_injective (p : Nat.Primes) :
    Function.Injective (primeZmodUnitAddCirclePhaseHom p) := by
  letI : NeZero p.1 := ⟨p.2.ne_zero⟩
  intro x y hxy
  apply ZMod.injective_toCircle
  exact (AddCircle.homeomorphCircle one_ne_zero).symm.injective hxy

/-- An additive phase observable vanishes on a whole prime polygon exactly when it vanishes on
the primitive phase. -/
theorem primeTorsionPhaseRestriction_eq_zero_hasse_iff
    (p : Nat.Primes) {A : Type*} [AddGroup A] (F : UnitAddCircle →+ A) :
    F.comp (primeZmodUnitAddCirclePhaseHom p) = 0 ↔
      F (primeZmodUnitAddCirclePhaseHom p 1) = 0 := by
  exact GaloisForLFunctions.HTGeometry.ABHN.zmodPrime_addMonoidHom_eq_zero_iff_apply_one_eq_zero
    p (F.comp (primeZmodUnitAddCirclePhaseHom p))

/-- Two additive phase observables agree on a whole prime polygon exactly when they agree on its
primitive phase. -/
theorem primeTorsionPhaseRestriction_congr_hasse_iff
    (p : Nat.Primes) {A : Type*} [AddGroup A] (F G : UnitAddCircle →+ A) :
    F.comp (primeZmodUnitAddCirclePhaseHom p) =
        G.comp (primeZmodUnitAddCirclePhaseHom p) ↔
      F (primeZmodUnitAddCirclePhaseHom p 1) =
        G (primeZmodUnitAddCirclePhaseHom p 1) := by
  exact GaloisForLFunctions.HTGeometry.ABHN.zmodPrime_addMonoidHom_eq_iff_apply_one_eq
    p (F.comp (primeZmodUnitAddCirclePhaseHom p))
      (G.comp (primeZmodUnitAddCirclePhaseHom p))

/-- The restriction of an additive phase observable to a prime polygon is faithful exactly when
the primitive phase survives. -/
theorem primeTorsionPhaseRestriction_injective_hasse_iff
    (p : Nat.Primes) {A : Type*} [AddGroup A] (F : UnitAddCircle →+ A) :
    Function.Injective (F.comp (primeZmodUnitAddCirclePhaseHom p)) ↔
      F (primeZmodUnitAddCirclePhaseHom p 1) ≠ 0 := by
  exact GaloisForLFunctions.HTGeometry.ABHN.zmodPrime_addMonoidHom_injective_iff_apply_one_ne_zero
    p (F.comp (primeZmodUnitAddCirclePhaseHom p))

/-- Prime-torsion phase Hasse dichotomy: an additive observable either kills the entire polygon or
embeds it faithfully, and its primitive phase decides which. -/
theorem primeTorsionPhaseRestriction_trivial_or_faithful_hasse
    (p : Nat.Primes) {A : Type*} [AddGroup A] (F : UnitAddCircle →+ A) :
    (F.comp (primeZmodUnitAddCirclePhaseHom p) = 0 ∧
        F (primeZmodUnitAddCirclePhaseHom p 1) = 0) ∨
      (Function.Injective (F.comp (primeZmodUnitAddCirclePhaseHom p)) ∧
        F (primeZmodUnitAddCirclePhaseHom p 1) ≠ 0) := by
  exact GaloisForLFunctions.HTGeometry.ABHN.zmodPrime_addMonoidHom_trivial_or_faithful_hasse
    p (F.comp (primeZmodUnitAddCirclePhaseHom p))

end RHTower
