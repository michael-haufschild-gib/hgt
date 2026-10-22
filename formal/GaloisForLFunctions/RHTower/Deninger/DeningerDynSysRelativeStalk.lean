import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Topology.Sheaves.Stalks

/-!
# The relative local ring `𝒪_{X , y₀}` of §13.3

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §13.3.

For a morphism `π : X ⟶ X₀` and a point `y₀` of the base, `𝒪_{X , y₀}` denotes the stalk at `y₀`
of the pushforward `π_* 𝒪_X`, that is the colimit of `Γ(X , π⁻¹ U)` over the open neighbourhoods
`U` of `y₀`.  It receives the stalk of the base and maps to the stalk at every point above `y₀`,
and the composite of the two is the stalk map of `π`.  Composing further with the residue map
gives the evaluation `𝒪_{X , y₀} → κ (y)` appearing in diagram (148).
-/

namespace RHTower

open CategoryTheory AlgebraicGeometry TopCat.Presheaf

noncomputable section

universe u

variable {X X₀ : Scheme.{u}} (π : X ⟶ X₀)

/-- **Deninger, §13.3.**  The relative local ring `𝒪_{X , y₀}`: the stalk at `y₀` of the
pushforward of the structure sheaf. -/
def deningerRelStalk (y₀ : X₀) : CommRingCat.{u} :=
  (π.base _* X.presheaf).stalk y₀

/-- The sections over the preimage of an open neighbourhood map into the relative local ring. -/
def deningerRelGerm (U : X₀.Opens) (y₀ : X₀) (h : y₀ ∈ U) :
    Γ(X, π ⁻¹ᵁ U) ⟶ deningerRelStalk π y₀ :=
  (π.base _* X.presheaf).germ U y₀ h

/-- The structure map from the local ring of the base. -/
def deningerBaseToRelStalk (y₀ : X₀) : X₀.presheaf.stalk y₀ ⟶ deningerRelStalk π y₀ :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y₀).map π.c

/-- The map to the local ring at a point above. -/
def deningerRelStalkToStalk (y : X) : deningerRelStalk π (π.base y) ⟶ X.presheaf.stalk y :=
  X.presheaf.stalkPushforward CommRingCat.{u} π.base y

/-- **Deninger, §13.3, the left column of (148).**  The stalk map of `π` factors through the
relative local ring. -/
theorem deningerStalkMap_eq (y : X) :
    deningerBaseToRelStalk π (π.base y) ≫ deningerRelStalkToStalk π y = π.stalkMap y := rfl

/-- **Deninger, §13.3.**  Evaluation of a relative section at a point above `y₀`. -/
def deningerRelStalkToResidue (y : X) :
    deningerRelStalk π (π.base y) ⟶ X.residueField y :=
  deningerRelStalkToStalk π y ≫ X.residue y

theorem deningerRelStalkToResidue_eq (y : X) :
    deningerBaseToRelStalk π (π.base y) ≫ deningerRelStalkToResidue π y
      = π.stalkMap y ≫ X.residue y := by
  rw [deningerRelStalkToResidue, ← Category.assoc, deningerStalkMap_eq]

end

end RHTower

namespace RHTower

open CategoryTheory AlgebraicGeometry TopCat.Presheaf

noncomputable section

universe u

variable {X X₀ : Scheme.{u}} (π : X ⟶ X₀)

/-- **Deninger, §13.3.**  For `y₀` in the closure of `π (x)` the relative local ring at `y₀` maps
to the local ring at `x`. -/
def deningerRelStalkSpecializes {x : X} {y₀ : X₀} (h : π.base x ⤳ y₀) :
    deningerRelStalk π y₀ ⟶ X.presheaf.stalk x :=
  (π.base _* X.presheaf).stalkSpecializes h ≫ deningerRelStalkToStalk π x

/-- **Deninger, §13.3, the map `f ↦ f (x)` of diagram (148).**  Evaluation of a relative section
at a point of `X` whose image specializes to `y₀`. -/
def deningerRelEvalAt {x : X} {y₀ : X₀} (h : π.base x ⤳ y₀) :
    deningerRelStalk π y₀ ⟶ X.residueField x :=
  deningerRelStalkSpecializes π h ≫ X.residue x

theorem deningerRelEvalAt_eq {x : X} {y₀ : X₀} (h : π.base x ⤳ y₀) :
    deningerRelEvalAt π h
      = (π.base _* X.presheaf).stalkSpecializes h ≫ deningerRelStalkToResidue π x := by
  rw [deningerRelEvalAt, deningerRelStalkSpecializes, deningerRelStalkToResidue, Category.assoc]
  rfl

end

end RHTower
