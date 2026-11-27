import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.Profiles

/-! # Every call in a merger forest is the unique call across a cut -/
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.TreeLimits
open Temporal Temporal.Feedback
open private edge_labels from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentCuts
variable {V : Type*} [DecidableEq V]

/-- Recolor a component disjoint from the distinguished edge to
accommodate a new call without changing the separation. -/
private theorem extend_cut (l : V→V) (s : V→Bool) (q : V×V) {a b : V}
    (hq : l q.1=l q.2) (hs : s q.1≠s q.2) (ha : l a≠l q.1) (hab : l a≠l b) :
    ∃ c : V→Bool, c q.1≠c q.2 ∧ c a=c b ∧ ∀ i j, l i=l j → s i=s j → c i=c j := by
  let c (i : V) := if l i=l a then s b else s i
  refine ⟨c,?_,?_,?_⟩
  · simpa only [c,←hq,if_neg ha.symm] using hs
  · simp only [c,if_pos rfl,if_neg hab.symm]
  · intro i j h h'
    simp only [c,h,h']

/-- Deleting one designated call from a merger-only word separates
its endpoints, even if arbitrarily many later calls used those wires. -/
theorem single_crossing_in_forest (after before : List (V×V)) (q : V×V)
    (hw : redundant (after++q::before)=0) :
    ∃ c : V→Bool, c q.1≠c q.2 ∧ ∀ e∈after++before, c e.1=c e.2 := by
  classical
  induction after with
  | nil =>
    have hnew : ¬Nonmerging q before := by
      intro hh
      simp only [List.nil_append,redundant,if_pos hh] at hw
      omega
    let c (i : V) := decide (label before i=label before q.1)
    refine ⟨c,?_,?_⟩
    · have hne : label before q.2≠label before q.1 := Ne.symm hnew
      simp [c,hne]
    · intro e he
      simp only [c,edge_labels before e he]
  | cons e after ih =>
    let w := after++q::before
    change redundant (e::w)=0 at hw
    have hnew : ¬Nonmerging e w := by
      intro hh
      simp only [redundant,if_pos hh] at hw
      omega
    have hrest : redundant w=0 := by simpa only [redundant,if_neg hnew,Nat.add_zero] using hw
    obtain ⟨s,hs,hsep⟩ := ih hrest
    have hq := edge_labels w q (List.mem_append_right _ List.mem_cons_self)
    have sub (p : V×V) (hp : p∈after++before) : p∈w := by
      rcases List.mem_append.mp hp with h|h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have he : label w e.1≠label w e.2 := hnew
    have attach : ∃ c : V→Bool, c q.1≠c q.2 ∧ c e.1=c e.2 ∧
        ∀ i j, label w i=label w j → s i=s j → c i=c j := by
      by_cases h : label w e.1=label w q.1
      · obtain ⟨c,hc,hjoin,hr⟩ := extend_cut (label w) s q (a:=e.2) (b:=e.1) hq hs
          (fun h' => he (h.trans h'.symm)) he.symm
        exact ⟨c,hc,hjoin.symm,hr⟩
      · exact extend_cut (label w) s q hq hs h he
    obtain ⟨c,hc,hjoin,hr⟩ := attach
    refine ⟨c,hc,?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with h|h
    · subst p
      exact hjoin
    · exact hr _ _ (edge_labels w _ (sub _ h)) (hsep _ h)

#print axioms single_crossing_in_forest
end GaloisForLFunctions.HTGeometry.RepeatedGates.TreeLimits
