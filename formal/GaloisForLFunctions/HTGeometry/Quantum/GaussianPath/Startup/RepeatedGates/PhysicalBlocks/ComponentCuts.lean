import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PathCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.CausalSupport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.ComponentCount

/-! # Every new circuit component can be made to cross a path bond -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
open Temporal SpanningDensity
noncomputable section

/-- Give each newly encountered label the opposite color from its
predecessor. Its first occurrence then contributes a distinct change. -/
private theorem color_path {A : Type*} [DecidableEq A] (f : ℕ → A) (n : ℕ) :
    ∃ c : A → Bool, ((range (n+1)).image f).card ≤
      ((range n).filter fun k => c (f k)≠c (f (k+1))).card+1 := by
  induction n with
  | zero => exact ⟨fun _ => false,by simp⟩
  | succ n ih =>
    obtain ⟨c,hc⟩ := ih
    let F := (range (n+1)).image f
    let B := (range n).filter fun k => c (f k)≠c (f (k+1))
    have hF : ((range (n+1+1)).image f)=insert (f (n+1)) F := by
      rw [range_succ,image_insert]
    rw [hF]
    by_cases hnew : f (n+1)∈F
    · refine ⟨c,?_⟩
      rw [insert_eq_of_mem hnew]
      exact hc.trans (Nat.add_le_add_right (card_le_card (filter_subset_filter _ (range_mono (by omega)))) 1)
    · let c' := Function.update c (f (n+1)) (!(c (f n)))
      have hold {k : ℕ} (hk : k≤n) : c' (f k)=c (f k) := by
        have hne : f k≠f (n+1) := fun h => hnew (h ▸ mem_image_of_mem f (mem_range.mpr (by omega)))
        exact Function.update_of_ne hne ..
      let B' := (range (n+1)).filter fun k => c' (f k)≠c' (f (k+1))
      have hsub : insert n B ⊆ B' := by
        intro k hk
        rcases mem_insert.mp hk with hkn|hk
        · subst k
          refine mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩
          rw [hold (k:=n) le_rfl,show c' (f (n+1)) = !(c (f n)) from Function.update_self ..]
          cases c (f n) <;> decide
        · obtain ⟨hkr,hd⟩ := mem_filter.mp hk
          have hklt := mem_range.mp hkr
          exact mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [hold (k:=k) (by omega),hold (k:=k+1) (by omega)]⟩
      have hn : n∉B := fun h => (lt_irrefl n) (mem_range.mp (mem_filter.mp h).1)
      have hb := card_le_card hsub
      rw [card_insert_of_notMem hn] at hb
      refine ⟨c',?_⟩
      rw [card_insert_of_notMem hnew]
      change F.card≤B.card+1 at hc
      change F.card+1≤B'.card+1
      omega

private theorem edge_labels {V : Type*} [DecidableEq V] (w : List (V×V)) (p : V×V) (hp : p∈w) :
    label w p.1=label w p.2 := by
  induction w with
  | nil => cases hp
  | cons e w ih =>
    rcases List.mem_cons.mp hp with rfl|hw
    · simp [label]
    · simp only [label,ih hw]

/-- A circuit with k connected components admits a gate-respecting
cut crossing at least k−1 physical bonds. Contiguous components attain
this bound. The number of redundant gates is unrestricted. -/
theorem component_cut {n : ℕ} (C : TwoQubitCircuit (n+2)) :
    ∃ c : Cut C, (parts (circuitWord C)).card ≤ (crossed c).card+1 := by
  let w := circuitWord C
  let f (k : ℕ) := label w (Fin.ofNat (n+2) k)
  have hv {k : ℕ} (hk : k<n+2) : f k=label w ⟨k,hk⟩ :=
    congrArg (label w) (Fin.ext (Nat.mod_eq_of_lt hk))
  obtain ⟨b,hb⟩ := color_path f (n+1)
  let c : Cut C := ⟨fun i => b (label w i),by
    funext i
    have hi : C.architecture.sites i∈w := List.mem_map.mpr
      ⟨i,by simp,rfl⟩
    change xor (b (label w (C.architecture.sites i).1)) (b (label w (C.architecture.sites i).2))=false
    rw [edge_labels w _ hi]
    cases b (label w (C.architecture.sites i).2) <;> rfl⟩
  have hpart : parts w ⊆ (range (n+1+1)).image f := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨i.val,mem_range.mpr i.isLt,hv i.isLt⟩
  let g := Fin.ofNat (n+1)
  have hh : ((range (n+1)).filter fun k => b (f k)≠b (f (k+1))).card ≤ (crossed c).card := by
    apply card_le_card_of_injOn g
    · intro k hk
      obtain ⟨hkr,hne⟩ := mem_filter.mp hk
      have hlt := mem_range.mp hkr
      have hg : (g k).val=k := Nat.mod_eq_of_lt hlt
      apply (mem_crossed_iff c _).mpr
      change b (label w (g k).castSucc)≠b (label w (g k).succ)
      rw [hv (k:=k) (by omega),hv (k:=k+1) (by omega)] at hne
      have h₁ : (g k).castSucc=⟨k,by omega⟩ := Fin.ext hg
      have h₂ : (g k).succ=⟨k+1,by omega⟩ := Fin.ext (congrArg (·+1) hg)
      simpa only [h₁,h₂] using hne
    · intro i hi j hj h
      have hval := congrArg Fin.val h
      exact (Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hi).1)).symm.trans
        (hval.trans (Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hj).1)))
  exact ⟨c,(card_le_card hpart).trans (hb.trans (Nat.add_le_add_right hh 1))⟩

#print axioms component_cut
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
