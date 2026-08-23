/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.FiniteMilnorKTwoCharacterReciprocity
import GaloisForLFunctions.HTGeometry.FiniteMilnorKOneCharacterTransport

/-!
# The standard finite-field Milnor `K₁` invariant in `ℚ/ℤ`

Degree-one Milnor `K` theory of a finite field is finite cyclic, so it embeds additively in
`ℚ/ℤ`.  The canonical circle character used by the projective-line reciprocity modules is exactly
the standard `ℚ/ℤ` circle character after this embedding.  Naming the inner additive invariant
makes the completed-local reciprocity law available in ABHN's additive target.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The standard faithful `ℚ/ℤ` invariant of finite-field Milnor `K₁`. -/
noncomputable def finiteMilnorKOneStdRatModIntInvariant
    (F : Type*) [Field F] [Finite F] :
    MilnorKDeg F 1 →+ ABHN.RatModInt :=
  ABHN.finiteAddCyclicRatModIntAddHom _ (finiteMilnorKDegOne_isAddCyclic F)

/-- The standard finite-field Milnor `K₁` invariant is faithful. -/
theorem finiteMilnorKOneStdRatModIntInvariant_injective
    (F : Type*) [Field F] [Finite F] :
    Function.Injective (finiteMilnorKOneStdRatModIntInvariant F) :=
  ABHN.finiteAddCyclicRatModIntAddHom_injective _ (finiteMilnorKDegOne_isAddCyclic F)

/-- The standard `ℚ/ℤ` invariant vanishes exactly at the zero Milnor class. -/
theorem finiteMilnorKOneStdRatModIntInvariant_eq_zero_iff
    (F : Type*) [Field F] [Finite F] (x : MilnorKDeg F 1) :
    finiteMilnorKOneStdRatModIntInvariant F x = 0 ↔ x = 0 := by
  constructor
  · exact fun hx ↦ finiteMilnorKOneStdRatModIntInvariant_injective F
      (hx.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

/-- The canonical finite-field circle character factors through its additive `ℚ/ℤ` invariant. -/
theorem finiteMilnorKOneStdAddChar_eq_ratModInt_comp
    (F : Type*) [Field F] [Finite F] :
    finiteMilnorKOneStdAddChar F =
      ABHN.ratModIntStdAddChar.compAddMonoidHom
        (finiteMilnorKOneStdRatModIntInvariant F) :=
  rfl

/-- Transport the standard finite-field `ℚ/ℤ` invariant across a field equivalence. -/
noncomputable def finiteMilnorKOneStdRatModIntInvariantTransport
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B) :
    MilnorKDeg B 1 →+ ABHN.RatModInt :=
  (finiteMilnorKOneStdRatModIntInvariant A).comp
    (milnorKDegAddEquivOfRingEquiv e 1).symm.toAddMonoidHom

/-- The transported `ℚ/ℤ` invariant agrees with the source invariant. -/
theorem finiteMilnorKOneStdRatModIntInvariantTransport_apply_equiv
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B)
    (x : MilnorKDeg A 1) :
    finiteMilnorKOneStdRatModIntInvariantTransport e
        (milnorKDegAddEquivOfRingEquiv e 1 x) =
      finiteMilnorKOneStdRatModIntInvariant A x := by
  change finiteMilnorKOneStdRatModIntInvariant A
    ((milnorKDegAddEquivOfRingEquiv e 1).symm
      (milnorKDegAddEquivOfRingEquiv e 1 x)) = _
  rw [AddEquiv.symm_apply_apply]

/-- Transport preserves faithfulness of the finite-field `ℚ/ℤ` invariant. -/
theorem finiteMilnorKOneStdRatModIntInvariantTransport_injective
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B) :
    Function.Injective (finiteMilnorKOneStdRatModIntInvariantTransport e) :=
  (finiteMilnorKOneStdRatModIntInvariant_injective A).comp
    (milnorKDegAddEquivOfRingEquiv e 1).symm.injective

/-- The transported `ℚ/ℤ` invariant vanishes exactly at zero. -/
theorem finiteMilnorKOneStdRatModIntInvariantTransport_eq_zero_iff
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B)
    (x : MilnorKDeg B 1) :
    finiteMilnorKOneStdRatModIntInvariantTransport e x = 0 ↔ x = 0 := by
  constructor
  · exact fun hx ↦ finiteMilnorKOneStdRatModIntInvariantTransport_injective e
      (hx.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

/-- Circle-character transport is the standard character of additive-invariant transport. -/
theorem finiteMilnorKOneStdAddCharTransport_eq_ratModInt_comp
    {A B : Type*} [Field A] [Finite A] [Field B] (e : A ≃+* B) :
    finiteMilnorKOneStdAddCharTransport e =
      ABHN.ratModIntStdAddChar.compAddMonoidHom
        (finiteMilnorKOneStdRatModIntInvariantTransport e) :=
  rfl

end

end GaloisForLFunctions.HTGeometry
