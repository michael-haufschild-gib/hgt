import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Exact maximal line occupancy of a coordinate box

A nonhorizontal line has at most one point for each first coordinate; a
nonvertical line has at most one for each second coordinate. The coordinate
axes attain the maximal side length of every nonempty box.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset
open scoped Classical

variable {F : Type*} [Field F]

/-- Coordinate-box points on the affine line `A x + B y = C`. -/
def coordinateBoxLine (I J : Finset F) (A B C : F) : Finset (F × F) :=
  (I ×ˢ J).filter (fun z => A * z.1 + B * z.2 = C)

/-- Every nonhorizontal line has at most one box point above each first coordinate. -/
theorem coordinateBoxLine_card_le_first (I J : Finset F) (A B C : F) (hB : B ≠ 0) :
    (coordinateBoxLine I J A B C).card ≤ I.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro z hz
    exact (mem_product.mp (mem_filter.mp hz).1).1
  · intro x hx y hy hxy
    apply Prod.ext hxy
    apply mul_left_cancel₀ hB
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    linear_combination hx' - hy' - A * hxy

/-- Every nonvertical line has at most one box point beside each second coordinate. -/
theorem coordinateBoxLine_card_le_second (I J : Finset F) (A B C : F) (hA : A ≠ 0) :
    (coordinateBoxLine I J A B C).card ≤ J.card := by
  apply card_le_card_of_injOn Prod.snd
  · intro z hz
    exact (mem_product.mp (mem_filter.mp hz).1).2
  · intro x hx y hy hxy
    apply Prod.ext _ hxy
    apply mul_left_cancel₀ hA
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    linear_combination hx' - hy' - B * hxy

/-- Oblique lines satisfy both side bounds simultaneously. -/
theorem coordinateBoxLine_card_le_min (I J : Finset F) (A B C : F)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    (coordinateBoxLine I J A B C).card ≤ min I.card J.card :=
  le_min (coordinateBoxLine_card_le_first I J A B C hB)
    (coordinateBoxLine_card_le_second I J A B C hA)

/-- All affine lines have occupancy at most the larger side length. -/
theorem coordinateBoxLine_card_le_max (I J : Finset F) (A B C : F)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    (coordinateBoxLine I J A B C).card ≤ max I.card J.card := by
  rcases hAB with hA | hB
  · exact (coordinateBoxLine_card_le_second I J A B C hA).trans (le_max_right _ _)
  · exact (coordinateBoxLine_card_le_first I J A B C hB).trans (le_max_left _ _)

/-- Horizontal lines through the box attain its first side length. -/
theorem coordinateBoxLine_horizontal (I J : Finset F) (c : F) (hc : c ∈ J) :
    coordinateBoxLine I J 0 1 c = I ×ˢ {c} := by
  ext ⟨a, b⟩
  simp only [coordinateBoxLine, mem_filter, mem_product, zero_mul, one_mul,
    zero_add, mem_singleton]
  constructor
  · rintro ⟨⟨ha, _⟩, rfl⟩
    exact ⟨ha, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨⟨ha, hc⟩, rfl⟩

/-- Vertical lines through the box attain its second side length. -/
theorem coordinateBoxLine_vertical (I J : Finset F) (c : F) (hc : c ∈ I) :
    coordinateBoxLine I J 1 0 c = {c} ×ˢ J := by
  ext ⟨a, b⟩
  simp only [coordinateBoxLine, mem_filter, mem_product, zero_mul, one_mul,
    add_zero, mem_singleton]
  constructor
  · rintro ⟨⟨_, hb⟩, rfl⟩
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨⟨hc, hb⟩, rfl⟩

/-- The larger side length is the exact maximum, not just an upper bound. -/
theorem coordinateBoxLine_max_attained (I J : Finset F) (hI : I.Nonempty) (hJ : J.Nonempty) :
    ∃ A B C : F, (A ≠ 0 ∨ B ≠ 0) ∧
      (coordinateBoxLine I J A B C).card = max I.card J.card := by
  rcases le_total I.card J.card with h | h
  · obtain ⟨c, hc⟩ := hI
    refine ⟨1, 0, c, Or.inl one_ne_zero, ?_⟩
    rw [coordinateBoxLine_vertical I J c hc, card_product, card_singleton,
      one_mul, max_eq_right h]
  · obtain ⟨c, hc⟩ := hJ
    refine ⟨0, 1, c, Or.inr one_ne_zero, ?_⟩
    rw [coordinateBoxLine_horizontal I J c hc, card_product, card_singleton,
      mul_one, max_eq_left h]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
