import GaloisForLFunctions.RHTower.MaassHomogeneousSpaceCorrespondence
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Equiv

/-!
# Automorphic functions as a coinduced representation

For a subgroup `Γ ≤ SL(2, ℝ)`, Mathlib's algebraic coinduction from the trivial representation of
`Γ` consists exactly of left `Γ`-invariant functions on `SL(2, ℝ)`.  This file identifies that
coinduced representation with the right regular representation used by the homogeneous-space
Maass correspondence.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Trivial one-dimensional complex representation of `Γ`. -/
abbrev trivialSubgroupRepresentation (Γ : Subgroup SL2R) :
    Representation ℂ Γ ℂ :=
  Representation.trivial ℂ Γ ℂ

/-- Algebraically coinduced representation space from the trivial representation of `Γ`. -/
abbrev coinducedAutomorphicFunctionSpace (Γ : Subgroup SL2R) : Type :=
  Representation.coindV Γ.subtype (trivialSubgroupRepresentation Γ)

/-- Left `Γ`-invariant functions are exactly Mathlib's coinduced vectors. -/
def automorphicFunctionSpaceEquivCoinduced (Γ : Subgroup SL2R) :
    automorphicFunctionSpace Γ ≃ₗ[ℂ] coinducedAutomorphicFunctionSpace Γ where
  toFun F :=
    ⟨F.1, by
      intro γ g
      simpa using F.property γ g⟩
  invFun F :=
    ⟨F.1, by
      intro γ g
      simpa using F.property γ g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem automorphicFunctionSpaceEquivCoinduced_apply (Γ : Subgroup SL2R)
    (F : automorphicFunctionSpace Γ) (g : SL2R) :
    (automorphicFunctionSpaceEquivCoinduced Γ F).1 g = F.1 g :=
  rfl

/-- Mathlib coinduction and the right regular action on `Γ \ SL(2, ℝ)` are equivalent as
representations of `SL(2, ℝ)`. -/
def automorphicRightRegularEquivCoinduced (Γ : Subgroup SL2R) :
    (automorphicRightRegularRepresentation Γ).Equiv
      (Representation.coind Γ.subtype (trivialSubgroupRepresentation Γ)) :=
  Representation.Equiv.mk (automorphicFunctionSpaceEquivCoinduced Γ) (by
    intro h
    ext F g
    rfl)

@[simp]
theorem automorphicRightRegularEquivCoinduced_apply (Γ : Subgroup SL2R)
    (F : automorphicFunctionSpace Γ) (g : SL2R) :
    (automorphicRightRegularEquivCoinduced Γ F).1 g = F.1 g :=
  rfl

end

end GaloisForLFunctions.RHTower
