import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import GaloisForLFunctions.HTGeometry.FreeSimplicialBoundary

/-!
# The coproduct of copies of the base field is the free module

A coproduct of copies of the base field, indexed by a set, is the free module on that set: both
represent the same functor, taking a map out of them to a family of vectors indexed by the set.  The
identification carries the map induced by a map of index sets to the map induced on free modules, so
the free locally convex seminorms of the free module transport to the coproduct.

This is the identification of the chain spaces of a singular chain complex with coefficients in the
base field — coproducts of copies of the field indexed by the singular simplices — with the free
modules on which the free locally convex direct sum topology is defined.

* `freeCoprodIso` : **the coproduct of copies of the field is the free module on the index set.**
* `ι_freeCoprodIso_hom` : it sends a summand to the corresponding generator.
* `freeCoprodIso_naturality` : **it carries `Sigma.map'` to `Finsupp.mapDomain`.**
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace GaloisForLFunctions

variable (𝕜 : Type) [NormedField 𝕜]

/-- **The coproduct of copies of the base field is the free module on the index set.** -/
def freeCoprodIso (α : Type) :
    (∐ fun _ : α => ModuleCat.of 𝕜 𝕜) ≅ ModuleCat.of 𝕜 (α →₀ 𝕜) where
  hom := Sigma.desc fun a => ModuleCat.ofHom (Finsupp.lsingle (R := 𝕜) (M := 𝕜) a)
  inv := ModuleCat.ofHom (Finsupp.lsum 𝕜 fun a =>
    (Sigma.ι (fun _ : α => ModuleCat.of 𝕜 𝕜) a).hom)
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun a => ?_
    rw [← Category.assoc, Sigma.ι_desc, Category.comp_id]
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    show Finsupp.lsum 𝕜 (fun a => (Sigma.ι (fun _ : α => ModuleCat.of 𝕜 𝕜) a).hom)
        (Finsupp.single a c) = (Sigma.ι (fun _ : α => ModuleCat.of 𝕜 𝕜) a).hom c
    rw [Finsupp.lsum_single]
  inv_hom_id := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun a => LinearMap.ext fun c => ?_)
    have hd : Sigma.ι (fun _ : α => ModuleCat.of 𝕜 𝕜) a ≫
        Sigma.desc (fun a => ModuleCat.ofHom (Finsupp.lsingle (R := 𝕜) (M := 𝕜) a))
        = ModuleCat.ofHom (Finsupp.lsingle (R := 𝕜) (M := 𝕜) a) := Sigma.ι_desc _ a
    have hval := congrArg
      (fun m : ModuleCat.of 𝕜 𝕜 ⟶ ModuleCat.of 𝕜 (α →₀ 𝕜) => m.hom c) hd
    show (Sigma.desc (fun a => ModuleCat.ofHom (Finsupp.lsingle (R := 𝕜) (M := 𝕜) a))).hom
        (Finsupp.lsum 𝕜 (fun a => (Sigma.ι (fun _ : α => ModuleCat.of 𝕜 𝕜) a).hom)
          (Finsupp.single a c)) = Finsupp.single a c
    rw [Finsupp.lsum_single]
    simpa [Finsupp.lsingle_apply] using hval

@[simp]
theorem ι_freeCoprodIso_hom {α : Type} (a : α) :
    Sigma.ι (fun _ : α => ModuleCat.of 𝕜 𝕜) a ≫ (freeCoprodIso 𝕜 α).hom
      = ModuleCat.ofHom (Finsupp.lsingle (R := 𝕜) (M := 𝕜) a) :=
  Sigma.ι_desc _ a

/-- **The identification carries the map induced by a map of index sets to the map induced on free
modules.** -/
theorem freeCoprodIso_naturality {α β : Type} (f : α → β) :
    (Sigma.map' f fun _ => 𝟙 (ModuleCat.of 𝕜 𝕜)) ≫ (freeCoprodIso 𝕜 β).hom
      = (freeCoprodIso 𝕜 α).hom ≫ ModuleCat.ofHom (Finsupp.lmapDomain 𝕜 𝕜 f) := by
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, Sigma.ι_comp_map', Category.assoc, ι_freeCoprodIso_hom,
    ← Category.assoc, ι_freeCoprodIso_hom, Category.id_comp]
  refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
  show Finsupp.single (f a) c = Finsupp.lmapDomain 𝕜 𝕜 f (Finsupp.single a c)
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end GaloisForLFunctions

end
