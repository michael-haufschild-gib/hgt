import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Short exactness of sheaves from short exactness of sections

A complex of presheaves of abelian groups is short exact as soon as it is short exact over every
object: monomorphisms and epimorphisms of natural transformations are detected objectwise, and a
kernel in a functor category is a kernel objectwise.  A complex of sheaves is short exact as soon
as the underlying complex of presheaves is, because the forgetful functor to presheaves is faithful
and additive.

* `deningerPresheafShortExact_of_app` : objectwise short exactness gives short exactness.
* `deningerSheafShortExact_of_forget` : short exactness descends from presheaves to sheaves.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v₁ u₁ u

/-- **Objectwise short exactness gives short exactness** in a functor category of abelian
groups. -/
theorem deningerPresheafShortExact_of_app {J : Type u₁} [Category.{v₁} J]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u}))
    (hmono : ∀ j, Mono (S.f.app j)) (hepi : ∀ j, Epi (S.g.app j))
    (hexact : ∀ j, (S.map ((evaluation J AddCommGrpCat.{u}).obj j)).Exact) :
    S.ShortExact := by
  haveI : ∀ j, Mono (S.f.app j) := hmono
  haveI : ∀ j, Epi (S.g.app j) := hepi
  haveI hm : Mono S.f := NatTrans.mono_of_mono_app _
  haveI he : Epi S.g := NatTrans.epi_of_epi_app _
  refine { exact := ?_, mono_f := hm, epi_g := he }
  refine ShortComplex.exact_of_f_is_kernel _ ?_
  refine evaluationJointlyReflectsLimits _ (fun j => ?_)
  refine (isLimitMapConeForkEquiv ((evaluation J AddCommGrpCat.{u}).obj j) _).symm ?_
  haveI : Mono ((S.map ((evaluation J AddCommGrpCat.{u}).obj j)).f) := hmono j
  exact (hexact j).fIsKernel

/-- **Short exactness descends from presheaves to sheaves.** -/
theorem deningerSheafShortExact_of_forget {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (h : (S.map (TopCat.Sheaf.forget AddCommGrpCat.{u} X)).ShortExact) : S.ShortExact :=
  CategoryTheory.ShortExact.reflects_shortExact_of_faithful _ h

end RHTower
