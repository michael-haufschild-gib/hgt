import GaloisForLFunctions.RHTower.DeningerHornLiftTwo
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# The map of classifying spaces of a surjection is a Kan fibration

Every horn of a classifying space maps into it, compatibly with a simplex below: a one dimensional
horn by surjectivity, a two dimensional horn by inverting an edge, and a horn of a simplex with at
least four vertices by reading the successive edges off the horn.  So the map of classifying spaces
induced by a surjective homomorphism has the right lifting property against all horn inclusions,
which is fibrancy in the Quillen model structure.

* `deningerClassifyingMap_hornLift` : the lifting property against every horn inclusion.
* `deningerClassifyingMap_fibration` : the map is a fibration.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite HomotopicalAlgebra SSet.modelCategoryQuillen

universe u

variable {G H : Type u} [Group G] [Group H]

/-- **The lifting property against every horn inclusion.** -/
theorem deningerClassifyingMap_hornLift (f : G →* H) (hf : Function.Surjective f) (n : ℕ)
    (i : Fin (n + 2)) :
    HasLiftingProperty (horn.{u} (n + 1) i).ι (deningerClassifyingMap f) := by
  constructor
  intro u v sq
  match n, i, u, v, sq with
  | 0, i, u, v, sq =>
    obtain ⟨l, h1, h2⟩ := deningerHornLift_one f hf i u v sq
    exact ⟨⟨l, h1, h2⟩⟩
  | 1, i, u, v, sq =>
    obtain ⟨l, h1, h2⟩ := deningerHornLift_two f i u v sq
    exact ⟨⟨l, h1, h2⟩⟩
  | (k + 2), i, u, v, sq =>
    obtain ⟨l, h1, h2⟩ := deningerHornLift_large (by omega) f i u v sq
    exact ⟨⟨l, h1, h2⟩⟩

/-- **The map of classifying spaces of a surjection is a Kan fibration.** -/
theorem deningerClassifyingMap_fibration (f : G →* H) (hf : Function.Surjective f) :
    Fibration (deningerClassifyingMap f) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B g hg
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, hn⟩ := hg
  cases hn with
  | mk i => exact deningerClassifyingMap_hornLift f hf n i

end RHTower
