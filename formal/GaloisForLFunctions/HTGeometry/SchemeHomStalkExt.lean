import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.Stalks

/-!
# A morphism of schemes is determined by its stalk maps

Two sections of the structure sheaf with the same germ at every point are equal, and the germ of
`f^♯ (s)` at `x` is the stalk map of `f` applied to the germ of `s` at `f (x)`.  So a morphism of
schemes is determined by its underlying continuous map together with the induced maps on stalks.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

/-- Two sections of the structure sheaf of a scheme with the same germ at every point of the open
set are equal. -/
theorem scheme_section_ext {X : Scheme.{u}} {U : X.Opens} {s t : X.presheaf.obj (op U)}
    (h : ∀ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx s = X.presheaf.germ U x hx t) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t h

/-- **A morphism of schemes is determined by its underlying map and its stalk maps.** -/
theorem scheme_hom_ext_of_stalkMap {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h_base : f.base = g.base)
    (h_stalk : ∀ (x : X) (U : Y.Opens) (hxf : f.base x ∈ U) (hxg : g.base x ∈ U)
      (y : Y.presheaf.obj (op U)),
      f.stalkMap x (Y.presheaf.germ U (f.base x) hxf y)
        = g.stalkMap x (Y.presheaf.germ U (g.base x) hxg y)) :
    f = g := by
  refine AlgebraicGeometry.Scheme.Hom.ext h_base fun U => ?_
  ext y
  refine scheme_section_ext fun x hx => ?_
  rw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res_apply',
    ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  exact h_stalk x U _ _ y

end HTGeometry
