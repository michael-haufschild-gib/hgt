import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PhysicalPatterns
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PacketMass

/-! # The external bonds of an arbitrary partition of the Pauli chain -/

open Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def sites (owner : Fin (n+2)→I) (i : I) : Finset (Fin (n+2)) := univ.filter fun v => owner v=i

def crosses (owner : Fin (n+2)→I) : PathLabel n→Prop
  | .inl _ => False
  | .inr (e,_) => owner e.castSucc≠owner e.succ

instance (owner : Fin (n+2)→I) : DecidablePred (crosses owner) :=
  fun q => by cases q <;> unfold crosses <;> infer_instance

def cutLabels (owner : Fin (n+2)→I) := univ.filter (crosses owner)

theorem sites_disjoint (owner : Fin (n+2)→I) : Pairwise fun i j => Disjoint (sites owner i) (sites owner j) :=
  fun _ _ h => disjoint_left.mpr fun _ hi hj => h ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)

theorem sites_longitudinal (owner : Fin (n+2)→I) (u : PathShell n) :
    (∑ i, longitudinal (sites owner i) u)=∑ v : Fin (n+2), |u (.inl (v,2))| := by
  simp only [longitudinal,sites,sum_filter]
  rw [sum_comm]
  simp

private theorem has_owner (owner : Fin (n+2)→I) {q : PathLabel n} (hc : q∉cutLabels owner) :
    ∃ i, PathWordSupportedIn (sites owner i) q := by
  rcases q with ⟨v,a⟩ | ⟨e,ab⟩
  · refine ⟨owner v,fun w hw => ?_⟩
    exact if_neg (fun he => hw (mem_filter.mpr ⟨mem_univ _,congrArg owner he⟩))
  · have he : owner e.castSucc=owner e.succ := by
      by_contra hn
      exact hc (mem_filter.mpr ⟨mem_univ _,hn⟩)
    refine ⟨owner e.castSucc,fun w hw => ?_⟩
    have h₁ : w≠e.castSucc := fun h => hw (mem_filter.mpr ⟨mem_univ _,congrArg owner h⟩)
    have h₂ : w≠e.succ := fun h => hw (mem_filter.mpr ⟨mem_univ _,(congrArg owner h).trans he.symm⟩)
    simp only [pathWord,couplingWord,if_neg h₁,if_neg h₂]

/-- Every changed interaction meeting an unchanged one touches a cut
bond on its unchanged side, independently of the binary pattern. -/
theorem outside_bond (owner : Fin (n+2)→I) (y : I→Bool) {q l : PathLabel n}
    (hq : q∉selectedLabels (sites owner) y) (hl : l∈selectedLabels (sites owner) y)
    (ho : l∈pathOverlaps q) : q∈cutLabels owner := by
  classical
  by_contra hc
  obtain ⟨i,hi⟩ := has_owner owner hc
  obtain ⟨j,hj,hs⟩ := (mem_filter.mp hl).2
  have hij : i=j := by
    obtain ⟨v,h₁,h₂⟩ := not_disjoint_iff.mp (mem_pathOverlaps.mp ho)
    have hw₁ : v∈sites owner i := Classical.byContradiction fun k => (mem_labelSupport.mp h₁) (hi v k)
    have hw₂ : v∈sites owner j := Classical.byContradiction fun k => (mem_labelSupport.mp h₂) (hs v k)
    exact (mem_filter.mp hw₁).2.symm.trans (mem_filter.mp hw₂).2
  exact hq (mem_filter.mpr ⟨mem_univ _,j,hj,hij ▸ hi⟩)

/-- Internal pattern labels never include any of the nine terms on a cut bond. -/
theorem internal_disjoint_cut (owner : Fin (n+2)→I) (y : I→Bool) :
    Disjoint (selectedLabels (sites owner) y) (cutLabels owner) := by
  classical
  apply disjoint_left.mpr
  rintro (⟨v,a⟩ | ⟨e,ab⟩) hl hc
  · exact (mem_filter.mp hc).2
  · obtain ⟨i,_,hi⟩ := (mem_filter.mp hl).2
    have hleft : e.castSucc∈sites owner i := by
      by_contra hn
      have h := hi e.castSucc hn
      simpa [pathWord,couplingWord] using h
    have hright : e.succ∈sites owner i := by
      by_contra hn
      have h := hi e.succ hn
      have hne : e.succ≠e.castSucc := fun h => by have hh := congrArg Fin.val h; simp at hh
      simpa [pathWord,couplingWord,hne] using h
    exact (mem_filter.mp hc).2 ((mem_filter.mp hleft).2.trans (mem_filter.mp hright).2.symm)

#print axioms outside_bond
#print axioms internal_disjoint_cut
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
