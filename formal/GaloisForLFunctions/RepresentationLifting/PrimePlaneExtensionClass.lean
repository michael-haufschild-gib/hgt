import GaloisForLFunctions.RepresentationLifting.PrimePlaneLocalSplitting
import GaloisForLFunctions.RepresentationLifting.RepresentationExt

/-!
# A nonzero self-extension class vanishing on every cyclic subgroup

For every odd prime, the prime-plane norm module has a nonzero class in
`Ext¹(V,V)` whose image under restriction to every cyclic subgroup is zero.
Nonvanishing follows from the incompatible local retraction traces; local
vanishing follows from the explicit cyclic splittings and naturality of Ext.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace GaloisForLFunctions.RepresentationLifting

variable (p : ℕ) [Fact p.Prime]

/-- The degree-one self-extension class of the prime-plane norm module. -/
def primePlaneExtensionClass :
    Ext (primePlaneSelfExtension p).X₃ (primePlaneSelfExtension p).X₁ 1 :=
  (primePlaneSelfExtension_shortExact p).extClass

/-- For every odd prime, the explicit self-extension defines a nonzero Ext class. -/
theorem primePlaneExtensionClass_ne_zero (hp : p ≠ 2) : primePlaneExtensionClass p ≠ 0 := by
  intro h
  exact primePlaneSelfExtension_not_split p hp
    ((extClass_zero_iff_retraction _ (primePlaneSelfExtension_shortExact p)).mp h)

/-- Every cyclic restriction kills this nonzero global extension class. -/
theorem primePlaneExtensionClass_cyclic_zero (hp : p ≠ 2)
    (H : Subgroup (Multiplicative (ZMod p) × Multiplicative (ZMod p))) [IsCyclic H] :
    (primePlaneExtensionClass p).mapExactFunctor (Rep.resFunctor H.subtype) = 0 := by
  change (primePlaneSelfExtension_shortExact p).extClass.mapExactFunctor (Rep.resFunctor H.subtype) = 0
  rw [Ext.mapExactFunctor_extClass]
  exact (extClass_zero_iff_retraction _ _).mpr (primePlaneSelfExtension_cyclic_splits p hp H)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.primePlaneExtensionClass_ne_zero
#print axioms GaloisForLFunctions.RepresentationLifting.primePlaneExtensionClass_cyclic_zero
