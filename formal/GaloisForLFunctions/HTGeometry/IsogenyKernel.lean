import GaloisForLFunctions.HTGeometry.IsogenyGeneral
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Isogenies and their kernels

Surjective isogenies out of a fixed commutative group are classified by their kernels: the
quotient by a finite subgroup is a surjective isogeny of degree the order of that subgroup, and
every surjective isogeny factors through the quotient by its kernel via an isomorphism.

The two extreme invariants also read off directly: a homomorphism is injective exactly when its
kernel has order one, and surjective exactly when its cokernel has order one, so it is bijective
exactly when both invariants are trivial.
-/

open Subgroup

variable {G H : Type*} [CommGroup G] [CommGroup H]

namespace MonoidHom

@[to_additive]
theorem kerCard_eq_one_iff (f : G →* H) : f.kerCard = 1 ↔ Function.Injective f := by
  rw [kerCard, Subgroup.card_eq_one, MonoidHom.ker_eq_bot_iff]

@[to_additive]
theorem cokerCard_eq_one_iff (f : G →* H) : f.cokerCard = 1 ↔ Function.Surjective f := by
  rw [cokerCard, Subgroup.index_eq_one, MonoidHom.range_eq_top]

@[to_additive]
theorem bijective_iff_kerCard_and_cokerCard (f : G →* H) :
    Function.Bijective f ↔ f.kerCard = 1 ∧ f.cokerCard = 1 := by
  rw [kerCard_eq_one_iff, cokerCard_eq_one_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

end MonoidHom

namespace QuotientGroup

/-- The quotient map by a finite subgroup is a surjective isogeny. -/
@[to_additive /-- The quotient map by a finite subgroup is a surjective isogeny. -/]
theorem isIsogeny_mk' (N : Subgroup G) [Finite N] : IsIsogeny (QuotientGroup.mk' N) :=
  IsIsogeny.of_surjective (QuotientGroup.mk'_surjective N)
    (by rw [QuotientGroup.ker_mk']; infer_instance)

@[to_additive]
theorem kerCard_mk' (N : Subgroup G) : (QuotientGroup.mk' N).kerCard = Nat.card N := by
  rw [MonoidHom.kerCard, QuotientGroup.ker_mk']

/-- The degree of the quotient isogeny is the order of the subgroup divided out. -/
@[to_additive /-- The degree of the quotient isogeny is the order of the subgroup divided
out. -/]
theorem isogenyDegree_mk' (N : Subgroup G) :
    (QuotientGroup.mk' N).isogenyDegree = (Nat.card N : ℚ) := by
  rw [MonoidHom.isogenyDegree_of_surjective (QuotientGroup.mk'_surjective N), kerCard_mk']

/-- **Every surjective isogeny is the quotient by its kernel.**  The comparison map is an
isomorphism making the triangle commute. -/
@[to_additive /-- **Every surjective additive isogeny is the quotient by its kernel.** -/]
theorem exists_mulEquiv_comp_mk' {f : G →* H} (hs : Function.Surjective f) :
    ∃ e : G ⧸ f.ker ≃* H,
      (e : G ⧸ f.ker →* H).comp (QuotientGroup.mk' f.ker) = f := by
  refine ⟨QuotientGroup.quotientKerEquivOfSurjective f hs, ?_⟩
  ext x
  rfl

end QuotientGroup
