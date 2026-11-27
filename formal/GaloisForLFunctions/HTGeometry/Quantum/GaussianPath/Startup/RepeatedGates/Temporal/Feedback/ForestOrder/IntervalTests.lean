import Mathlib.Order.Interval.Set.OrdConnected

/-! # Four compatible classes of missing pairs separated by intervals -/
open Set
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {J : Type*}

/-- The interval contains a source and every tested sink it can reach,
while omitting its own sink. Interchanging sources and sinks gives the
opposite orientation of a separating cut. -/
def intervalTrap (a b : J→ℕ) (R : J→J→Prop) (i : J) :=
  ∃ I : Set ℕ, I.OrdConnected ∧ a i∈I ∧ b i∉I ∧ ∀ j, R i j → b j∈I

private theorem no_swap (a b : J→ℕ) (R : J→J→Prop) {i j : J}
    (hi : intervalTrap a b R i) (hj : intervalTrap a b R j)
    (hdir : (a i≤b i ↔ a j≤b j)) (hij : R i j) (hji : R j i) : False := by
  obtain ⟨I,hI,ha,hb,hreach⟩ := hi
  obtain ⟨T,hT,ha',hb',hreach'⟩ := hj
  by_cases h : a i≤b i
  · have hl : b j<b i := lt_of_not_ge fun hle => hb (hI.out ha (hreach j hij) ⟨h,hle⟩)
    exact hb' (hT.out ha' (hreach' i hji) ⟨hdir.mp h,hl.le⟩)
  · have hl : b i<b j := lt_of_not_ge fun hle => hb (hI.out (hreach j hij) ha ⟨hle,(lt_of_not_ge h).le⟩)
    exact hb' (hT.out (hreach' i hji) ha' ⟨hl.le,(lt_of_not_ge (fun hp => h (hdir.mpr hp))).le⟩)

/-- Missing pairs are colored by the side trapped by the cut and the
direction of separation in the vertex order. Mutual cross-connections
would force each of the two outside endpoints to precede the other. -/
theorem four_classes (a b : J→ℕ) (R : J→J→Prop)
    (h : ∀ i, intervalTrap a b R i ∨ intervalTrap b a (fun j k => R k j) i) :
    ∃ c : J→Bool×Bool, ∀ i j, c i=c j → ¬(R i j ∧ R j i) := by
  classical
  let P := intervalTrap a b R
  let c (i : J) := (decide (P i),if P i then decide (a i≤b i) else decide (b i≤a i))
  refine ⟨c,?_⟩
  intro i j he hr
  have hp : P i ↔ P j := by simpa [c] using congrArg Prod.fst he
  have hc := congrArg Prod.snd he
  by_cases hi : P i
  · have hj := hp.mp hi
    exact no_swap a b R hi hj (by simpa [c,hi,hj] using hc) hr.1 hr.2
  · have hj : ¬P j := fun h => hi (hp.mpr h)
    exact no_swap b a (fun k l => R l k) ((h i).resolve_left hi) ((h j).resolve_left hj)
      (by simpa [c,hi,hj] using hc) hr.2 hr.1

#print axioms four_classes
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
