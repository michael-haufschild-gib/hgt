import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

/-! # Consecutive ranks for finite nested families -/
open Set Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {V : Type*}

/-- A finite family whose members are nested whenever they meet. -/
def NestedFamily (F : Finset (Finset V)) :=
  ∀ A∈F, ∀ B∈F, A⊆B ∨ B⊆A ∨ Disjoint A B

/-- A laminar family is the pullback of integer intervals under one rank
map. Equal membership patterns receive equal ranks. Inserting a smallest
set splits just one old rank, leaving every old interval consecutive. -/
theorem laminar_intervals (F : Finset (Finset V)) : NestedFamily F →
    ∃ r : V→ℕ, (∀ x y, (∀ S∈F, x∈S ↔ y∈S) → r x=r y) ∧
      ∀ S∈F, ∃ I : Set ℕ, I.OrdConnected ∧ ∀ x, r x∈I ↔ x∈S := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    intro h
    obtain he|hne := F.eq_empty_or_nonempty
    · subst F; exact ⟨fun _ => 0,fun _ _ _ => rfl,by simp⟩
    obtain ⟨S,hS,hmin⟩ := F.exists_min_image Finset.card hne
    let G := F.erase S
    have hg : G ⊂ F := erase_ssubset hS
    obtain ⟨r,heq,hI⟩ := ih G hg (fun A ha B hb => h A (hg.le ha) B (hg.le hb))
    let f x := 2*r x + if x∈S then 0 else 1
    have half (x) : f x/2=r x := by dsimp only [f]; split <;> omega
    have old (x y : V) (hx : x∈S) (hy : y∈S) : r x=r y := by
      apply heq
      intro T ht
      obtain hST|hTS|hd := h S hS T (hg.le ht)
      · exact ⟨fun _ => hST hy,fun _ => hST hx⟩
      · exact False.elim ((mem_erase.mp ht).1 (eq_of_subset_of_card_le hTS (hmin T (hg.le ht))))
      · exact iff_of_false (disjoint_left.mp hd hx) (disjoint_left.mp hd hy)
    refine ⟨f,?_,?_⟩
    · intro x y hw
      have hr := heq x y (fun T ht => hw T (hg.le ht))
      simp only [f,hr,hw S hS]
    · intro T ht
      by_cases hT : T=S
      · subst T
        obtain hse|hsp := S.eq_empty_or_nonempty
        · exact ⟨∅,ordConnected_empty,by simp [hse]⟩
        obtain ⟨x,hx⟩ := hsp
        refine ⟨{2*r x},ordConnected_singleton,?_⟩
        intro y
        change f y=2*r x ↔ _
        by_cases hy : y∈S
        · simp [f,hy,old y x hy hx]
        · simp [f,hy]; omega
      · obtain ⟨I,hconn,hmem⟩ := hI T (mem_erase.mpr ⟨hT,ht⟩)
        refine ⟨(fun z : ℕ => z/2) ⁻¹' I,hconn.preimage_mono (fun _ _ hxy => by omega),?_⟩
        intro x
        simpa only [mem_preimage,half] using hmem x

#print axioms laminar_intervals
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
