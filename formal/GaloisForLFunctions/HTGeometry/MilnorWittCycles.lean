import GaloisForLFunctions.HTGeometry.MilnorWittFundamentalClass
import Mathlib.Data.DFinsupp.Module
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Milnor--Witt cycles in codimension one

A codimension-one cycle with Milnor--Witt coefficients is a finitely supported family assigning to
each closed point a class in `K_0^{MW}` of its residue field, twisted by the conormal line of the
point.  The twist is essential: there is no canonical generator of that line, and a change of
generator moves the coefficient by a unit form.

The rank descends to the twist without choosing any generator, because the rank does not see unit
forms.  So a Milnor--Witt cycle has a well-defined underlying ordinary cycle, and this is the
forgetful map from oriented to ordinary intersection theory in codimension one.

* `ClosedPoint`, `MWPointGroup` : the points and their twisted coefficient groups.
* `MWCycles`, `Cycles` : **the Milnor--Witt and the ordinary codimension-one cycle groups.**
* `mwCyclesRank` : **the underlying ordinary cycle of a Milnor--Witt cycle.**
-/

namespace GaloisForLFunctions.HTGeometry

attribute [local instance] Ideal.Quotient.field Classical.propDecidable

section Cycles

/-- A closed point of `Spec S`. -/
structure ClosedPoint (S : Type*) [CommRing S] where
  /-- The maximal ideal of the point. -/
  ideal : Ideal S
  /-- It is maximal. -/
  isMaximal : ideal.IsMaximal

attribute [instance] ClosedPoint.isMaximal

variable {S : Type*} [CommRing S]

/-- The twisted Milnor--Witt coefficient group at a closed point: `K_0^{MW}` of the residue field,
twisted by the conormal line of the point. -/
abbrev MWPointGroup (p : ClosedPoint S) : Type _ :=
  MWLineTwist (S ⧸ p.ideal) 0 (Ideal.Cotangent p.ideal)

variable (S)

/-- **The Milnor--Witt cycle group in codimension one.** -/
abbrev MWCycles : Type _ := Π₀ p : ClosedPoint S, MWPointGroup p

/-- **The ordinary cycle group in codimension one.** -/
abbrev Cycles : Type _ := Π₀ _ : ClosedPoint S, ℤ

variable {S}

/-- The Milnor--Witt cycle supported at one closed point. -/
noncomputable def mwCycleSingle (p : ClosedPoint S) (x : MWPointGroup p) : MWCycles S :=
  DFinsupp.single p x

/-- The ordinary cycle of a closed point with a multiplicity. -/
noncomputable def cycleSingle (p : ClosedPoint S) (n : ℤ) : Cycles S :=
  DFinsupp.single p n

variable (S)

/-- **The underlying ordinary cycle of a Milnor--Witt cycle**, taken pointwise.  No generator of
any conormal line is chosen: the rank is invariant under the unit forms. -/
noncomputable def mwCyclesRank : MWCycles S →+ Cycles S :=
  DFinsupp.mapRange.addMonoidHom fun p : ClosedPoint S => (mwTwistRank : MWPointGroup p →+ ℤ)

variable {S}

@[simp]
theorem mwCyclesRank_single (p : ClosedPoint S) (x : MWPointGroup p) :
    mwCyclesRank S (mwCycleSingle p x) = cycleSingle p (mwTwistRank x) :=
  DFinsupp.mapRange_single (hf := fun _ => map_zero _)

/-- **The Gysin pushforward of the closed immersion of a point**, on codimension-one cycles: a
twisted Milnor--Witt class at the point becomes the cycle supported there.  For a regular closed
immersion of codimension one this is the whole pushforward: the points of the closed subscheme are
points of the ambient one, and the determinant twist is transported along the conormal
trivialization. -/
noncomputable def mwGysin (p : ClosedPoint S) : MWPointGroup p →+ MWCycles S :=
  DFinsupp.singleAddHom (fun q : ClosedPoint S => MWPointGroup q) p

@[simp]
theorem mwGysin_apply (p : ClosedPoint S) (x : MWPointGroup p) :
    mwGysin p x = mwCycleSingle p x := rfl

/-- **The Gysin pushforward is injective**: no information is lost. -/
theorem mwGysin_injective (p : ClosedPoint S) : Function.Injective (mwGysin p) :=
  fun _ _ h => DFinsupp.single_injective h

/-- **The Gysin pushforward covers the ordinary pushforward**: taking the underlying ordinary cycle
of a Gysin image is the ordinary cycle of the point with the rank as multiplicity. -/
theorem mwCyclesRank_mwGysin (p : ClosedPoint S) (x : MWPointGroup p) :
    mwCyclesRank S (mwGysin p x) = cycleSingle p (mwTwistRank x) :=
  mwCyclesRank_single p x

/-- **The forgetful map onto ordinary cycles is surjective** as soon as every closed point has a
nonzero conormal class: the unit orientation placed at such a class has rank one, so every ordinary
cycle is the underlying cycle of a Milnor--Witt one. -/
theorem mwCyclesRank_surjective
    (h : ∀ p : ClosedPoint S, ∃ e : Ideal.Cotangent p.ideal, e ≠ 0) :
    Function.Surjective (mwCyclesRank S) := by
  intro c
  induction c using DFinsupp.induction with
  | h0 => exact ⟨0, map_zero _⟩
  | ha p n c _ _ ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨e, he⟩ := h p
      refine ⟨n • mwCycleSingle p
        (mwTwistMk (S ⧸ p.ideal) 0 (MWLinePoints (S ⧸ p.ideal) (Ideal.Cotangent p.ideal))
          ⟨e, he⟩ mwOne) + x, ?_⟩
      rw [map_add, hx, map_zsmul, mwCyclesRank_single, mwTwistRank_mk, mwRank_mwOne]
      show (n • cycleSingle p 1) + c = DFinsupp.single p n + c
      rw [cycleSingle, ← DFinsupp.single_smul, smul_eq_mul, mul_one]

end Cycles

end GaloisForLFunctions.HTGeometry
