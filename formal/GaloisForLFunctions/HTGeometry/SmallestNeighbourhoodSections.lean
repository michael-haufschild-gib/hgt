import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Sections over a smallest open neighbourhood are the stalk

The stalk of a presheaf at `x` is the colimit over the open neighbourhoods of `x`.  If `x` has a
smallest open neighbourhood `V`, that indexing category has a terminal object, so the germ map on
the sections over `V` is an isomorphism.
-/

namespace HTGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u v

/-- If `V` is the smallest open neighbourhood of `x`, the germ map at `x` on the sections over `V`
is an isomorphism: the stalk is a colimit over a category with a terminal object. -/
theorem isIso_germ_of_isMin {C : Type u} [Category.{v} C] [HasColimits C]
    {X : TopCat} (F : TopCat.Presheaf C X) (V : Opens X) (x : X) (hx : x ∈ V)
    (hmin : ∀ W : Opens X, x ∈ W → V ≤ W) : IsIso (F.germ V x hx) := by
  have hterm : IsTerminal (op (⟨V, hx⟩ : OpenNhds x)) := by
    refine IsTerminal.ofUniqueHom
      (fun W => (homOfLE (hmin W.unop.1 W.unop.2) : (⟨V, hx⟩ : OpenNhds x) ⟶ W.unop).op) ?_
    intro W f
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  exact isIso_ι_of_isTerminal hterm _

end HTGeometry
