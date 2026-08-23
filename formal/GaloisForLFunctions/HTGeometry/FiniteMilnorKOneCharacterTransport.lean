/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.FiniteMilnorKTwoCharacterReciprocity
import GaloisForLFunctions.HTGeometry.MilnorKDegRingEquiv

/-!
# Transporting the canonical finite-field Milnor `K₁` character

A field equivalence from a finite field transports its canonical injective circle character to
degree-one Milnor `K` theory of the target field.  This isolates the functorial step needed when a
global residue field is identified with the residue field of its completion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Transport the canonical finite-field Milnor `K₁` circle character across a field equivalence. -/
noncomputable def finiteMilnorKOneStdAddCharTransport
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B) :
    AddChar (MilnorKDeg B 1) ℂ :=
  (finiteMilnorKOneStdAddChar A).compAddMonoidHom
    (milnorKDegAddEquivOfRingEquiv e 1).symm.toAddMonoidHom

/-- The transported character agrees with the source character after applying the equivalence. -/
theorem finiteMilnorKOneStdAddCharTransport_apply_equiv
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B) (x : MilnorKDeg A 1) :
    finiteMilnorKOneStdAddCharTransport e (milnorKDegAddEquivOfRingEquiv e 1 x) =
      finiteMilnorKOneStdAddChar A x := by
  change finiteMilnorKOneStdAddChar A
    ((milnorKDegAddEquivOfRingEquiv e 1).symm (milnorKDegAddEquivOfRingEquiv e 1 x)) = _
  rw [AddEquiv.symm_apply_apply]

/-- Transport preserves faithfulness of the canonical finite-field Milnor `K₁` character. -/
theorem finiteMilnorKOneStdAddCharTransport_injective
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B) :
    Function.Injective (finiteMilnorKOneStdAddCharTransport e) :=
  (finiteMilnorKOneStdAddChar_injective A).comp
    (milnorKDegAddEquivOfRingEquiv e 1).symm.injective

/-- The transported finite-field phase is one exactly at the zero Milnor `K₁` class. -/
theorem finiteMilnorKOneStdAddCharTransport_eq_one_iff_eq_zero
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B) (x : MilnorKDeg B 1) :
    finiteMilnorKOneStdAddCharTransport e x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    apply finiteMilnorKOneStdAddCharTransport_injective e
    rw [hx]
    exact (finiteMilnorKOneStdAddCharTransport e).map_zero_eq_one.symm
  · intro hx
    rw [hx]
    exact (finiteMilnorKOneStdAddCharTransport e).map_zero_eq_one

end

end GaloisForLFunctions.HTGeometry
