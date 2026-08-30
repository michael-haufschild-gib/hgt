import Mathlib

/-!
# A transposition confines a block

If a permutation group preserving a block system contains a transposition, then any block meeting
one of the two swapped points but not the other is a singleton.  Equivalently: in a group with a
nontrivial block system, every transposition swaps two points of one block.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

/-- **A transposition confines a block.**  If `a ∈ B`, `b ∉ B` and the swap `(a b)` lies in a group
for which `B` is a block, then `B` is a singleton. -/
theorem subsingleton_of_isBlock_of_swap {X : Type*} [DecidableEq X]
    {G : Subgroup (Equiv.Perm X)} {B : Set X} (hB : MulAction.IsBlock G B)
    {a b : X} (hg : Equiv.swap a b ∈ G) (haB : a ∈ B) (hbB : b ∉ B) : B.Subsingleton := by
  by_contra hcon
  obtain ⟨c, hcB, hc'⟩ : ∃ c ∈ B, c ≠ a := by
    rw [Set.not_subsingleton_iff] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := hcon
    by_cases hxa : x = a
    · exact ⟨y, hy, fun h => hxy (by rw [hxa, h])⟩
    · exact ⟨x, hx, hxa⟩
  have hcb : c ≠ b := fun h => hbB (by rw [← h]; exact hcB)
  set g : G := ⟨Equiv.swap a b, hg⟩ with hgdef
  have hgc : g • c = c := by
    show Equiv.swap a b c = c
    exact Equiv.swap_apply_of_ne_of_ne hc' hcb
  have hmem : c ∈ g • B := ⟨c, hcB, hgc⟩
  have hne : ¬ Disjoint (g • B) ((1 : G) • B) := by
    rw [Set.not_disjoint_iff]
    refine ⟨c, hmem, ?_⟩
    rw [one_smul]
    exact hcB
  have heq : g • B = (1 : G) • B := by
    by_contra h
    exact hne (hB h)
  rw [one_smul] at heq
  refine hbB ?_
  rw [← heq]
  exact ⟨a, haB, by show Equiv.swap a b a = b; exact Equiv.swap_apply_left a b⟩

/-- **Every transposition of a group with a nontrivial block lies inside one block.** -/
theorem mem_block_of_isBlock_of_swap {X : Type*} [DecidableEq X]
    {G : Subgroup (Equiv.Perm X)} {B : Set X} (hB : MulAction.IsBlock G B)
    (hBne : ¬ B.Subsingleton) {a b : X} (hg : Equiv.swap a b ∈ G) (haB : a ∈ B) : b ∈ B := by
  by_contra hbB
  exact hBne (subsingleton_of_isBlock_of_swap hB hg haB hbB)

end GaloisForLFunctions.HTGeometry
