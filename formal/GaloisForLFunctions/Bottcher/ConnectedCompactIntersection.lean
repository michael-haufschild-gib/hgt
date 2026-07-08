import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sets.Compacts

open Topology Set

namespace Bottcher

/-- A downward-directed intersection of compact preconnected sets is preconnected. -/
theorem isPreconnected_iInter_antitone {X ι : Type*} [TopologicalSpace X] [T2Space X]
    [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    {K : ι → Set X} (hanti : Antitone K) (hcomp : ∀ i, IsCompact (K i))
    (hconn : ∀ i, IsPreconnected (K i)) :
    IsPreconnected (⋂ i, K i) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hCcompact : IsCompact (⋂ i, K i) :=
    (hcomp i₀).of_isClosed_subset (isClosed_iInter fun i => (hcomp i).isClosed) (iInter_subset _ i₀)
  rw [isPreconnected_closed_iff]
  intro t u ht hu hcover htne hune
  by_contra hne'
  rw [not_nonempty_iff_eq_empty] at hne'
  have hCt : IsCompact ((⋂ i, K i) ∩ t) := hCcompact.inter_right ht
  have hCu : IsCompact ((⋂ i, K i) ∩ u) := hCcompact.inter_right hu
  have hdisj : Disjoint ((⋂ i, K i) ∩ t) ((⋂ i, K i) ∩ u) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← hne']; ext x; simp only [mem_inter_iff]; tauto
  obtain ⟨U, V, hU, hV, hCtU, hCuV, hUVdisj⟩ := SeparatedNhds.of_isCompact_isCompact hCt hCu hdisj
  have hCUV : (⋂ i, K i) ⊆ U ∪ V := by
    intro x hx
    rcases hcover hx with hxt | hxu
    · exact Or.inl (hCtU ⟨hx, hxt⟩)
    · exact Or.inr (hCuV ⟨hx, hxu⟩)
  by_cases hall : ∀ i, (K i ∩ (U ∪ V)ᶜ).Nonempty
  · have hdir : Directed (· ⊇ ·) (fun i => K i ∩ (U ∪ V)ᶜ) := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      exact ⟨k, inter_subset_inter_left _ (hanti hik), inter_subset_inter_left _ (hanti hjk)⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun i => K i ∩ (U ∪ V)ᶜ) hdir hall
      (fun i => (hcomp i).inter_right (hU.union hV).isClosed_compl)
      (fun i => (hcomp i).isClosed.inter (hU.union hV).isClosed_compl)
    rw [mem_iInter] at hx
    have hxC : x ∈ ⋂ i, K i := by rw [mem_iInter]; exact fun i => (hx i).1
    exact (hx i₀).2 (hCUV hxC)
  · simp only [not_forall, not_nonempty_iff_eq_empty] at hall
    obtain ⟨i₁, hi₁⟩ := hall
    have hKUV : K i₁ ⊆ U ∪ V := by
      intro x hx
      by_contra hxUV
      have hmem : x ∈ K i₁ ∩ (U ∪ V)ᶜ := ⟨hx, hxUV⟩
      rw [hi₁] at hmem; exact hmem
    have hKU : (K i₁ ∩ U).Nonempty := by
      obtain ⟨x, hx⟩ := htne
      exact ⟨x, iInter_subset _ i₁ hx.1, hCtU hx⟩
    have hKV : (K i₁ ∩ V).Nonempty := by
      obtain ⟨x, hx⟩ := hune
      exact ⟨x, iInter_subset _ i₁ hx.1, hCuV hx⟩
    obtain ⟨x, hx⟩ := hconn i₁ U V hU hV hKUV hKU hKV
    have hxU : x ∈ U := Set.mem_of_mem_inter_left (Set.mem_of_mem_inter_right hx)
    have hxV : x ∈ V := Set.mem_of_mem_inter_right (Set.mem_of_mem_inter_right hx)
    exact Set.disjoint_left.mp hUVdisj hxU hxV

end Bottcher
