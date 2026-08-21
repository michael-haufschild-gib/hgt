import GaloisForLFunctions.HTGeometry.ZerothHomology

/-!
# Chains split over a clopen decomposition

The topological simplex is convex, hence connected, so the image of a singular simplex is connected
and must lie entirely inside one piece of a disjoint open cover.  The chains supported in the two
pieces are therefore complementary submodules of the chains of the whole space in every degree.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

instance preconnectedSpace_topSimplex (k : ℕ) : PreconnectedSpace (topSimplex k) :=
  isPreconnected_iff_preconnectedSpace.mp (convex_stdSimplex ℝ (Fin (k + 1))).isPreconnected

theorem smallChain_of_clopen_pair {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : (Set.univ : Set X) ⊆ U ∪ V) {k : ℕ}
    (c : C(topSimplex k, X) →₀ R) : SmallChain R {U, V} c := by
  intro σ _
  have hconn : IsPreconnected (Set.range σ) := isPreconnected_range σ.continuous
  rcases hconn.subset_or_subset hU hV hdisj (fun y _ => hcover (Set.mem_univ y)) with h | h
  · exact ⟨U, Or.inl rfl, h⟩
  · exact ⟨V, Or.inr rfl, h⟩

theorem subChains_sup_eq_top {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : (Set.univ : Set X) ⊆ U ∪ V) (k : ℕ) :
    subChains R U k ⊔ subChains R V k = ⊤ := by
  refine eq_top_iff.mpr fun c _ => ?_
  exact (smallChain_pair_iff R U V c).mp (smallChain_of_clopen_pair R hU hV hdisj hcover c)

theorem subChains_empty (k : ℕ) : subChains R (∅ : Set X) k = ⊥ := by
  refine eq_bot_iff.mpr fun c hc => ?_
  rw [mem_subChains] at hc
  rw [Submodule.mem_bot]
  by_contra hne
  obtain ⟨σ, hσ⟩ := Finsupp.support_nonempty_iff.mpr hne
  exact (hc σ hσ) ⟨stdSimplex.vertex 0, rfl⟩

theorem subChains_inf_eq_bot {U V : Set X} (hdisj : Disjoint U V) (k : ℕ) :
    subChains R U k ⊓ subChains R V k = ⊥ := by
  rw [← subChains_inter, Set.disjoint_iff_inter_eq_empty.mp hdisj, subChains_empty]

theorem isCompl_subChains {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : (Set.univ : Set X) ⊆ U ∪ V) (k : ℕ) :
    IsCompl (subChains R U k) (subChains R V k) :=
  ⟨disjoint_iff.mpr (subChains_inf_eq_bot R hdisj k),
    codisjoint_iff.mpr (subChains_sup_eq_top R hU hV hdisj hcover k)⟩

end GaloisForLFunctions.HTGeometry
