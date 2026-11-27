import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.Cuts.Glue
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.CrossConnections

/-! # The input relation and component certificates of a word of mergers -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {V : Type*} [DecidableEq V]

/-- At either joining output the two previous input sets are pooled. -/
def Joined (R : V→V→Prop) (a b i j : V) := R i j ∨ ((j=a ∨ j=b) ∧ (R i a ∨ R i b))

omit [DecidableEq V] in
private theorem joined_swap (R : V→V→Prop) (a b : V) : Joined R a b=Joined R b a := by
  funext i j
  exact propext (or_congr Iff.rfl (and_congr or_comm or_comm))

private theorem joined_side {R : V→V→Prop} {A : Finset V} {a b : V} (hb : b∉A)
    (h : ∀ i j, R i j → (i∈A ↔ j∈A)) : SideRule R (Joined R a b) A a := by
  intro i j hij
  rcases hij with hr|⟨hj,hr⟩
  · by_cases hi : i∈A
    · exact Or.inl ⟨hi,(h i j hr).mp hi,hr⟩
    · exact Or.inr ⟨fun hx => (hi hx).elim,fun hx => (hi ((h i j hr).mpr hx)).elim⟩
  · refine Or.inr ⟨fun hi => hr.resolve_right (fun hh => hb ((h i b hh).mp hi)),?_⟩
    intro hx
    exact hj.resolve_right (fun he => hb (he ▸ hx))

private theorem joined_back {R : V→V→Prop} {A : Finset V} {a b : V} (i j : V)
    (hj : j∈A ∨ j=b) (hr : R i (if j∈A then j else a)) : Joined R a b i j := by
  by_cases hin : j∈A
  · exact Or.inl (by simpa only [if_pos hin] using hr)
  · exact Or.inr ⟨Or.inr (hj.resolve_left hin),Or.inl (by simpa only [if_neg hin] using hr)⟩

omit [DecidableEq V] in
/-- Replacing a relation by another one agreeing inside a component
preserves every separator, including its orientation. -/
theorem cutFamily_congr {R T : V→V→Prop} {C : Finset V} {F : Finset (Finset (Port V))}
    (h : ∀ i∈C, ∀ j∈C, R i j ↔ T i j) (hf : CutFamily R C F) : CutFamily T C F := by
  refine ⟨hf.1,hf.2.1,?_⟩
  intro i hi j hj hm
  obtain ⟨S,hS,hh⟩ := hf.2.2 i hi j hj (fun he => hm ((h i hi j hj).mp he))
  refine ⟨S,hS,?_⟩
  rcases hh with ⟨hx,hy,he⟩|⟨hx,hy,he⟩
  · exact Or.inl ⟨hx,hy,fun x hx y hy hxy => he x hx y hy ((h x hx y hy).mpr hxy)⟩
  · exact Or.inr ⟨hx,hy,fun x hx y hy hxy => he x hx y hy ((h x hx y hy).mpr hxy)⟩

variable [Fintype V]

def wires (w : List (V×V)) (l : V) := univ.filter fun i => label w i=l

@[simp] theorem mem_wires {w : List (V×V)} {l i : V} : i∈wires w l ↔ label w i=l := by
  simp only [wires,mem_filter,mem_univ,true_and]

private def Reach (w : List (V×V)) (i j : V) := i∈inputs w j

omit [Fintype V] in
private theorem reach_join (w : List (V×V)) (a b : V) :
    Reach ((a,b)::w)=Joined (Reach w) a b := by
  funext i j
  apply propext
  by_cases hj : j=a ∨ j=b
  · simp only [Reach,inputs,Joined,hj,ite_true,mem_union,true_and]
    constructor
    · exact Or.inr
    · rintro (h|h)
      · rcases hj with rfl|rfl
        · exact Or.inl h
        · exact Or.inr h
      · exact h
  · simp only [Reach,inputs,Joined,hj,ite_false,false_and,or_false]

private theorem wires_closed (w : List (V×V)) (l i j : V) (h : Reach w i j) :
    i∈wires w l ↔ j∈wires w l := by simp only [mem_wires,label_of_input w h]

omit [DecidableEq V] [Fintype V] in
private theorem empty_cuts (R : V→V→Prop) (C : Finset V) (h : ∀ i∈C, ∀ j∈C, R i j) :
    CutFamily R C ∅ := by
  refine ⟨by simp [NestedFamily],by simp,?_⟩
  intro i hi j hj hm
  exact (hm (h i hi j hj)).elim

/-- Each component of a merger-only word admits a nested family of
one-way cuts separating every unreachable source from its sink. -/
theorem component_cuts (w : List (V×V)) (hw : redundant w=0) (l : V) :
    ∃ F, CutFamily (fun i j => i∈inputs w j) (wires w l) F := by
  change ∃ F, CutFamily (Reach w) _ F
  induction w generalizing l with
  | nil =>
    refine ⟨∅,empty_cuts _ _ ?_⟩
    intro i hi j hj
    exact mem_singleton.mpr ((mem_wires.mp hi).trans (mem_wires.mp hj).symm)
  | cons e w ih =>
    obtain ⟨a,b⟩ := e
    have hprev : redundant w=0 := (Nat.add_eq_zero_iff.mp hw).1
    have hab : label w a≠label w b := by
      intro h
      have hn : Nonmerging (a,b) w := h
      simp only [redundant,if_pos hn,Nat.add_one_ne_zero] at hw
    let A := wires w (label w a)
    let B := wires w (label w b)
    have ha : a∈A := mem_wires.mpr rfl
    have hb : b∈B := mem_wires.mpr rfl
    have hd : Disjoint A B := disjoint_left.mpr (fun _ h h' => hab ((mem_wires.mp h).symm.trans (mem_wires.mp h')))
    rw [reach_join]
    by_cases hl : l=label w a
    · subst l
      have hun : wires ((a,b)::w) (label w a)=A∪B := by
        ext x
        simp only [mem_wires,mem_union,A,B,label]
        by_cases hx : label w x=label w b <;> simp [hx]
      rw [hun]
      obtain ⟨F,hF⟩ := ih hprev (label w a)
      obtain ⟨G,hG⟩ := ih hprev (label w b)
      have hs := joined_side (a:=a) (disjoint_left.mp hd.symm hb) (wires_closed w _)
      have ht := joined_side (a:=b) (disjoint_left.mp hd ha) (wires_closed w _)
      refine join_cut_families ha hb hd hF hG hs (by rw [joined_swap (Reach w) a b]; exact ht) ?_ ?_
      · exact fun i _ j hj => joined_back i j hj
      · rw [joined_swap (Reach w) a b]
        exact fun i _ j hj => joined_back i j hj
    · by_cases hB : l=label w b
      · subst l
        refine ⟨∅,empty_cuts _ _ ?_⟩
        intro i hi
        have hh := mem_wires.mp hi
        simp only [label] at hh
        split at hh <;> contradiction
      · have he : wires ((a,b)::w) l=wires w l := by
          ext i
          simp only [mem_wires,label]
          by_cases hx : label w i=label w b <;> simp [hx,Ne.symm hl,Ne.symm hB]
        rw [he]
        obtain ⟨F,hF⟩ := ih hprev l
        refine ⟨F,cutFamily_congr ?_ hF⟩
        intro i _ j hj
        have hj' := mem_wires.mp hj
        have hn : ¬(j=a ∨ j=b) := fun hh => hh.elim (fun h => hl (hj'.symm.trans (congrArg (label w) h)))
          (fun h => hB (hj'.symm.trans (congrArg (label w) h)))
        simp only [Joined,hn,false_and,or_false]

#print axioms component_cuts
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
