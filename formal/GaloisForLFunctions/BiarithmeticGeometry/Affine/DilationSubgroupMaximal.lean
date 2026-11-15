import GaloisForLFunctions.ArithmeticPositiveDuality.AMautnerPhenomenonForTheAffineGroupOfQ
import Mathlib.Order.Atoms

/-!
# The dilation subgroup is maximal in the rational affine group

The point-stabilizer mechanism of Bardyla--Elliott--Péresse,
arXiv:2608.28211, applies to the corpus's rational affine action.
The stabilizer of zero is exactly the dilation subgroup. Any affine map
outside it supplies a nonzero translation; conjugating by dilations supplies
every rational translation. In particular the integer successor and all
dilations generate the entire affine group.
-/

noncomputable section
open GaloisForLFunctions.ArithmeticPositiveDuality
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The dilation subgroup is exactly the stabilizer of the rational origin. -/
theorem mem_dilation_range_iff (g : AffineGroupQ) :
    g ∈ dilation.range ↔ affShift g = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact affShift_dilation u
  · intro h
    rw [eq_translation_mul_dilation g, h, translation_zero, one_mul]
    exact ⟨_, rfl⟩

/-- Every proper enlargement of the dilation subgroup is the full affine group. -/
theorem dilation_range_isCoatom : IsCoatom dilation.range := by
  constructor
  · intro htop
    have hmem : translation 1 ∈ dilation.range := by rw [htop]; trivial
    have hzero := (mem_dilation_range_iff _).mp hmem
    rw [affShift_translation] at hzero
    exact one_ne_zero hzero
  · intro H hH
    obtain ⟨g, hg, hng⟩ := SetLike.exists_of_lt hH
    have hg0 : affShift g ≠ 0 := fun h => hng ((mem_dilation_range_iff g).mpr h)
    have hd (u : ℚˣ) : dilation u ∈ H := hH.le ⟨u, rfl⟩
    let u := Units.mk0 (affSlope g) (affSlope_ne_zero g)
    have hgdec : g = translation (affShift g) * dilation u := eq_translation_mul_dilation g
    have ht : translation (affShift g) ∈ H := by
      have hm := H.mul_mem hg (H.inv_mem (hd u))
      rw [hgdec, mul_inv_cancel_right] at hm
      exact hm
    have htranslation (b : ℚ) : translation b ∈ H := by
      by_cases hb : b = 0
      · rw [hb, translation_zero]
        exact H.one_mem
      let v : ℚˣ := Units.mk0 (b / affShift g) (div_ne_zero hb hg0)
      have hm := H.mul_mem (H.mul_mem (hd v) ht) (H.inv_mem (hd v))
      rw [dilation_mul_translation_mul_inv] at hm
      change translation (b / affShift g * affShift g) ∈ H at hm
      rwa [div_mul_cancel₀ _ hg0] at hm
    apply top_unique
    intro f _
    rw [eq_translation_mul_dilation f]
    exact H.mul_mem (htranslation _) (hd _)

/-- There are exactly two subgroups containing every rational dilation. -/
theorem dilation_overgroups (H : Subgroup AffineGroupQ) :
    dilation.range ≤ H ↔ H = dilation.range ∨ H = ⊤ := by
  constructor
  · intro h
    rcases eq_or_lt_of_le h with he | ht
    · exact Or.inl he.symm
    · exact Or.inr (dilation_range_isCoatom.2 H ht)
  · rintro (rfl | rfl)
    · exact le_rfl
    · exact le_top

/-- A single integer successor, together with dilations, generates all rational affine maps. -/
theorem dilations_and_successor_generate :
    Subgroup.closure ((dilation.range : Set AffineGroupQ) ∪ {successor}) = ⊤ := by
  have hle : dilation.range ≤
      Subgroup.closure ((dilation.range : Set AffineGroupQ) ∪ {successor}) :=
    fun _ hx => Subgroup.subset_closure (Or.inl hx)
  rcases (dilation_overgroups _).mp hle with h | h
  · have hs : successor ∈ dilation.range := by
      rw [← h]
      exact Subgroup.subset_closure (Or.inr rfl)
    have hz := (mem_dilation_range_iff successor).mp hs
    have hone : affShift successor = 1 := by
      change successor 0 = 1
      rw [successor_apply, add_zero]
    exact False.elim (one_ne_zero (hone.symm.trans hz))
  · exact h

end GaloisForLFunctions.BiarithmeticGeometry
