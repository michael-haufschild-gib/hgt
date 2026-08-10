import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Milman's partial converse to the Krein–Milman theorem

If `A` is compact and the closed convex hull `K` of `A` is compact, then every extreme point of `K`
already lies in `A`.

The proof is Rudin's: given a convex neighbourhood `V` of the origin, cover `A` by finitely many
translates `a + V`, replace each piece by the closed convex hull of `A ∩ (a + closure V)`, and
observe that the convex hull of finitely many nonempty compact convex sets is compact — hence
closed, hence contains `K`.  An extreme point of `K` lying in such a hull must lie in one of the
pieces, so it lies in `A + closure V`; letting `V` shrink puts it in `A`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The convex join of two compact sets is compact: it is the image of `[0,1] × s × t` under the
segment map. -/
theorem isCompact_convexJoin {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  have hEq : convexJoin ℝ s t
      = (fun p : ℝ × E × E => (1 - p.1) • p.2.1 + p.1 • p.2.2) '' (Icc 0 1 ×ˢ s ×ˢ t) := by
    ext z
    constructor
    · rw [mem_convexJoin]
      rintro ⟨a, ha, b, hb, hz⟩
      rw [segment_eq_image] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      exact ⟨(θ, a, b), ⟨hθ, ha, hb⟩, rfl⟩
    · rintro ⟨⟨θ, a, b⟩, ⟨hθ, ha, hb⟩, rfl⟩
      rw [mem_convexJoin]
      refine ⟨a, ha, b, hb, ?_⟩
      rw [segment_eq_image]
      exact ⟨θ, hθ, rfl⟩
  rw [hEq]
  exact (isCompact_Icc.prod (hs.prod ht)).image (by fun_prop)

/-- The convex hull of a finite family of nonempty compact convex sets is compact. -/
theorem isCompact_convexHull_biUnion {ι : Type*} [DecidableEq ι] (t : Finset ι) (K : ι → Set E)
    (hne : ∀ i ∈ t, (K i).Nonempty) (hc : ∀ i ∈ t, IsCompact (K i))
    (hconv : ∀ i ∈ t, Convex ℝ (K i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ t, K i)) := by
  induction t using Finset.induction with
  | empty => simpa using isCompact_empty
  | insert b t hb ih =>
      have hbmem : b ∈ insert b t := Finset.mem_insert_self b t
      have hsub : ∀ i ∈ t, i ∈ insert b t := fun i hi => Finset.mem_insert_of_mem hi
      have hKb : IsCompact (K b) := hc b hbmem
      have hKbconv : Convex ℝ (K b) := hconv b hbmem
      have hKbne : (K b).Nonempty := hne b hbmem
      have hUnion : (⋃ i ∈ insert b t, K i) = K b ∪ ⋃ i ∈ t, K i := by
        simp [Finset.set_biUnion_insert]
      rcases t.eq_empty_or_nonempty with rfl | htne
      · rw [hUnion]
        simpa [hKbconv.convexHull_eq] using hKb
      · have hrest := ih (fun i hi => hne i (hsub i hi)) (fun i hi => hc i (hsub i hi))
          (fun i hi => hconv i (hsub i hi))
        obtain ⟨j, hj⟩ := htne
        have hUne : (⋃ i ∈ t, K i).Nonempty := by
          obtain ⟨z, hz⟩ := hne j (hsub j hj)
          exact ⟨z, Set.mem_biUnion hj hz⟩
        rw [hUnion, convexHull_union hKbne hUne, hKbconv.convexHull_eq]
        exact isCompact_convexJoin hKb hrest

end GaloisForLFunctions.HTGeometry
