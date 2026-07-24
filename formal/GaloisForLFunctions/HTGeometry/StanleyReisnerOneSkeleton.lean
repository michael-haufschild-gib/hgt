import GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation
import GaloisForLFunctions.HTGeometry.ReducedH0Components

/-!
# The 1-skeleton graph of a complex and its disconnect cycles

The reduced-`H̃⁰` of a finite complex is governed by the connected components of its 1-skeleton — the
graph whose edges are the two-element faces.  This file records that graph and connects it to the
Stanley–Reisner Koszul cycles: two vertices in different connected components of the 1-skeleton form
a nonface pair, so the base-to-component disconnect cycle joining them is a first Koszul cycle.

This is the bridge between the algebraic degree-0 Hochster data (`srDisconnectCycle`,
`srDisconnectCycle_independent_mod_koszulBoundary`) and the combinatorial reduced-`H̃⁰` side
(`componentConstant`, `finrank_reducedH0`): the independent Koszul classes are indexed by the
non-base connected components of this graph.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial SimpleGraph

noncomputable section

variable {R α : Type*} [CommRing R] [DecidableEq α]

/-- The 1-skeleton graph of a finite complex: two distinct vertices are adjacent exactly when their
pair is a face (an edge of the complex). -/
def oneSkeletonGraph (facets : Finset (Finset α)) : SimpleGraph α where
  Adj u v := u ≠ v ∧ IsFaceOf (↑facets : Set (Finset α)) {u, v}
  symm := fun _ _ h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Two vertices in different connected components of the 1-skeleton form a nonface pair: were their
pair a face, they would be adjacent, hence reachable. -/
theorem not_isFace_of_not_reachable (facets : Finset (Finset α)) {v₀ w : α}
    (hnr : ¬ (oneSkeletonGraph facets).Reachable v₀ w) :
    ¬ IsFaceOf (↑facets : Set (Finset α)) {w, v₀} := by
  intro hf
  have hne : w ≠ v₀ := by rintro rfl; exact hnr (Reachable.refl _)
  have hadj : (oneSkeletonGraph facets).Adj w v₀ := ⟨hne, hf⟩
  exact hnr hadj.reachable.symm

variable [Fintype α]

/-- **Graph form of the disconnect-cycle law.**  When the base vertex `v₀` and the target `w` lie in
different connected components of the 1-skeleton, the base-to-`w` disconnect cycle is a first Koszul
cycle of the Stanley–Reisner ring.  This indexes the reduced-`H̃⁰` Koszul classes by the non-base
components of `oneSkeletonGraph`. -/
theorem srKoszulRelation_disconnectCycle_of_not_reachable (facets : Finset (Finset α)) {v₀ w : α}
    (hnr : ¬ (oneSkeletonGraph facets).Reachable v₀ w) :
    srKoszulRelation facets (srDisconnectCycle R facets v₀ w) = 0 := by
  have hne : w ≠ v₀ := by rintro rfl; exact hnr (Reachable.refl _)
  exact srKoszulRelation_disconnectCycle facets hne (not_isFace_of_not_reachable facets hnr)

end

end GaloisForLFunctions.HTGeometry
