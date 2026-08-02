import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Subcomplexes form a distributive lattice

Meets and joins of subcomplexes are computed degreewise as intersections and unions of sets, so the
distributive law is inherited from sets.  The consequence used here is that a meet with a finite join
is controlled piece by piece: if every piece of the join meets a fixed subcomplex inside a bound, so
does the whole join.

That is what makes a many-piece cover foldable when the pieces meet each other only inside a fixed
base piece.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

variable {X : SSet.{u}}

/-- **The distributive law for subcomplexes**, from the degreewise distributive law for sets. -/
theorem Subcomplex.sup_inf_right (A B D : X.Subcomplex) :
    (A ⊔ B) ⊓ D = (A ⊓ D) ⊔ (B ⊓ D) := by
  ext k x
  simp
  tauto

/-- **A finite join meets a subcomplex inside any bound its pieces do.** -/
theorem finsetSup_inf_le {ι : Type*} (A : ι → X.Subcomplex) (D E : X.Subcomplex)
    (h : ∀ b, A b ⊓ D ≤ E) (s : Finset ι) : s.sup A ⊓ D ≤ E := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, bot_inf_eq]
      exact bot_le
  | insert a s _ ih =>
      rw [Finset.sup_insert, Subcomplex.sup_inf_right]
      exact sup_le (h a) ih

end GaloisForLFunctions.HTGeometry
