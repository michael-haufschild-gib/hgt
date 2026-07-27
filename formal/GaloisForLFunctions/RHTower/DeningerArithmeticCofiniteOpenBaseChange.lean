import Mathlib.Topology.LocalAtTarget

/-!
# Cofinite open base change for a coarse quotient

Deninger's arithmetic opens lift to saturated opens on the suspension
cover.  This file isolates the general topology used in the source
construction: the image of an open under an open quotient map is open,
restriction over that image remains an open quotient map, and a saturated
open is canonically the full restricted domain.

The arithmetic identification of Deninger's character spaces with these
saturated opens is the geometric input from Deninger's Lemmas 7.1--7.3 and
Proposition 7.4.  No derived invariants or quotient-stack cohomology occur.
-/

namespace RHTower

universe u v

section CofiniteOpenBaseChange

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- A source subset is saturated when it is the full inverse image of its
image in the coarse quotient. -/
def DeningerSaturatedOpen (q : X → Y) (V : Set X) : Prop :=
  q ⁻¹' (q '' V) = V

/-- Membership constant on every fibre makes a subset saturated. -/
theorem deningerSaturatedOpen_of_fiberwise
    (q : X → Y) (V : Set X)
    (hV : ∀ x y, q x = q y → (x ∈ V ↔ y ∈ V)) :
    DeningerSaturatedOpen q V := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (hV y x hyx).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- An open arithmetic lift has open image under an open coarse quotient
map. -/
theorem deningerSaturatedOpen_image_isOpen
    {q : X → Y} (hq : IsOpenQuotientMap q)
    {V : Set X} (hV : IsOpen V) :
    IsOpen (q '' V) :=
  hq.isOpenMap V hV

/-- Base change of an open quotient map to the image of a source open is
again an open quotient map. -/
theorem deningerSaturatedOpen_restrict_isOpenQuotientMap
    {q : X → Y} (hq : IsOpenQuotientMap q) (V : Set X) :
    IsOpenQuotientMap ((q '' V).restrictPreimage q) :=
  hq.restrictPreimage (q '' V)

/-- For a saturated source open, the domain of the restricted quotient map
is canonically homeomorphic to that open. -/
def deningerSaturatedOpenDomainHomeomorph
    {q : X → Y} {V : Set X} (hV : DeningerSaturatedOpen q V) :
    ↥(q ⁻¹' (q '' V)) ≃ₜ ↥V :=
  Homeomorph.setCongr hV

@[simp]
theorem deningerSaturatedOpenDomainHomeomorph_apply
    {q : X → Y} {V : Set X} (hV : DeningerSaturatedOpen q V)
    (x : ↥(q ⁻¹' (q '' V))) :
    (deningerSaturatedOpenDomainHomeomorph hV x : X) = x :=
  rfl

@[simp]
theorem deningerSaturatedOpenDomainHomeomorph_symm_apply
    {q : X → Y} {V : Set X} (hV : DeningerSaturatedOpen q V)
    (x : V) :
    ((deningerSaturatedOpenDomainHomeomorph hV).symm x : X) = x :=
  rfl

end CofiniteOpenBaseChange

end RHTower
