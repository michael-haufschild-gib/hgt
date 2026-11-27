import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.ForestCertificates
import Mathlib.Data.Int.Order.Basic

/-! # Strict increase along every cross-connection of a single color -/
open Set Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {J V : Type*}

private def forwardRank (u v : ℕ) : ℤ := if u≤v then -(v:ℤ) else (v:ℤ)

private theorem trap_rank_lt (a b : J→ℕ) (R : J→J→Prop) {i j : J}
    (h : intervalTrap a b R i) (hd : a i≤b i ↔ a j≤b j) (he : R i j) :
    forwardRank (a i) (b i)<forwardRank (a j) (b j) := by
  obtain ⟨I,hI,ha,hb,hs⟩ := h
  by_cases hi : a i≤b i
  · have hj := hd.mp hi
    have hl : b j<b i := lt_of_not_ge fun hle => hb (hI.out ha (hs j he) ⟨hi,hle⟩)
    simp only [forwardRank,if_pos hi,if_pos hj,neg_lt_neg_iff,Int.ofNat_lt]
    exact hl
  · have hj := fun hh => hi (hd.mpr hh)
    have hl : b i<b j := lt_of_not_ge fun hle => hb (hI.out (hs j he) ha ⟨hle,(lt_of_not_ge hi).le⟩)
    simp only [forwardRank,if_neg hi,if_neg hj,Int.ofNat_lt]
    exact hl

/-- Reversing the rank on sink-trapped pairs makes every connection
within a color point from smaller to larger integer rank. -/
theorem ordered_intervals (a b : J→ℕ) (R : J→J→Prop)
    (h : ∀ i, intervalTrap a b R i ∨ intervalTrap b a (fun j k => R k j) i) :
    ∃ (c : J→Bool×Bool) (r : J→ℤ), ∀ i j, c i=c j → R i j → r i<r j := by
  classical
  let P := intervalTrap a b R
  let c (i : J) := (decide (P i),if P i then decide (a i≤b i) else decide (b i≤a i))
  let r (i : J) := if P i then forwardRank (a i) (b i) else -forwardRank (b i) (a i)
  refine ⟨c,r,?_⟩
  intro i j he hij
  have hp : P i ↔ P j := by simpa [c] using congrArg Prod.fst he
  have hh := congrArg Prod.snd he
  by_cases hi : P i
  · have hj := hp.mp hi
    simpa only [r,if_pos hi,if_pos hj] using
      trap_rank_lt a b R hi (by simpa [c,hi,hj] using hh) hij
  · have hj := fun h => hi (hp.mpr h)
    have hd : b i≤a i ↔ b j≤a j := by simpa [c,hi,hj] using hh
    have hr := trap_rank_lt b a (fun k l => R l k) ((h j).resolve_left hj) hd.symm hij
    simpa only [r,if_neg hi,if_neg hj] using neg_lt_neg hr

/-- A single rank and four colors order every finite or infinite test
list on the wires of a merger-only circuit. -/
theorem forest_ordered_classes [DecidableEq V] [Fintype V] (w : List (V×V)) (hw : redundant w=0)
    (x y : J→V) (hm : ∀ i, x i∉inputs w (y i)) :
    ∃ (c : J→Bool×Bool) (z : J→ℤ), ∀ i j, c i=c j → x i∈inputs w (y j) → z i<z j := by
  obtain ⟨F,hF⟩ := forest_cuts w hw
  obtain ⟨r,_,hr⟩ := laminar_intervals F hF.1
  apply ordered_intervals (fun i => r (Sum.inl (x i))) (fun i => r (Sum.inr (y i)))
  intro i
  obtain ⟨S,hS,hs⟩ := hF.2.2 (x i) (mem_univ _) (y i) (mem_univ _) (hm i)
  obtain ⟨I,hI,hmem⟩ := hr S hS
  rcases hs with ⟨hx,hy,he⟩|⟨hx,hy,he⟩
  · exact Or.inl ⟨I,hI,(hmem _).mpr hx,fun hh => hy ((hmem _).mp hh),fun j hh =>
      (hmem _).mpr (he _ (mem_univ _) _ (mem_univ _) hh hx)⟩
  · exact Or.inr ⟨I,hI,(hmem _).mpr hy,fun hh => hx ((hmem _).mp hh),fun j hh =>
      (hmem _).mpr (he _ (mem_univ _) _ (mem_univ _) hh hy)⟩

#print axioms forest_ordered_classes
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
