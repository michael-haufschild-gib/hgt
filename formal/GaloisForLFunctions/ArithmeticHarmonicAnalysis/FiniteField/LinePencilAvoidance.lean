import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.CoordinateBoxLines
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Local counts for linear prime patterns

Avoiding lines through the origin separates into a nonzero scale and an
allowed slope. This gives the exact complement cardinality. For affine
forbidden values, the coordinate-box line bound gives a uniform union bound
and a local admissibility criterion.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

/-- Complement of the vertical axis and the lines with slopes in `S`. -/
def linePencilComplement (S : Finset F) : Finset (F × F) :=
  univ.filter (fun z => z.2 ≠ 0 ∧ ∀ a ∈ S, z.1 ≠ a * z.2)

/-- Nonzero scaling of an allowed slope parametrizes the complement exactly. -/
theorem linePencilComplement_eq_image (S : Finset F) :
    linePencilComplement S =
      ((univ \ S) ×ˢ (univ \ {0})).image (fun z : F × F => (z.1 * z.2, z.2)) := by
  ext ⟨x, y⟩
  simp only [linePencilComplement, mem_filter, mem_univ, true_and, mem_image,
    mem_product, mem_sdiff, mem_singleton]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨(x / y, y), ⟨?_, hy⟩, ?_⟩
    · intro ha
      exact h (x / y) ha (div_mul_cancel₀ x hy).symm
    · exact Prod.ext (div_mul_cancel₀ x hy) rfl
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, heq⟩
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    dsimp only at hx hy
    subst y
    refine ⟨hb, ?_⟩
    intro c hc hxc
    exact ha ((mul_right_cancel₀ hb (hx.trans hxc)).symm ▸ hc)

/-- Exact number of pairs on which all forms `y` and `x-ay` are nonzero. -/
theorem linePencilComplement_card (S : Finset F) :
    (linePencilComplement S).card =
      (Fintype.card F - S.card) * (Fintype.card F - 1) := by
  rw [linePencilComplement_eq_image, card_image_iff.mpr ?_, card_product]
  · simp [card_sdiff]
  · intro a ha b _ hab
    have ha₂ : a.2 ≠ 0 := by
      simpa only [mem_singleton] using (mem_sdiff.mp (mem_product.mp ha).2).2
    have h₂ := congrArg Prod.snd hab
    have h₁ := congrArg Prod.fst hab
    dsimp only at h₁ h₂
    apply Prod.ext _ h₂
    rw [← h₂] at h₁
    exact mul_right_cancel₀ ha₂ h₁

/-- Local admissibility for a pencil is equivalent to having an unused slope. -/
theorem linePencilComplement_nonempty_iff (S : Finset F) :
    (linePencilComplement S).Nonempty ↔ S.card < Fintype.card F := by
  rw [← card_pos, linePencilComplement_card]
  constructor
  · intro h
    have hne : Fintype.card F - S.card ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at h
      exact (lt_irrefl 0) h
    omega
  · intro h
    exact Nat.mul_pos (Nat.sub_pos_of_lt h) (Nat.sub_pos_of_lt Fintype.one_lt_card)

/-- The pencil count applies directly to the prime-pattern forms
`x`, `y`, and `x-λy`. -/
theorem mem_prime_pattern_pencil (S : Finset F) (x y : F) :
    (x, y) ∈ linePencilComplement (insert 0 S) ↔
      x ≠ 0 ∧ y ≠ 0 ∧ ∀ a ∈ S, x - a * y ≠ 0 := by
  simp only [linePencilComplement, mem_filter, mem_univ, true_and,
    mem_insert, forall_eq_or_imp, zero_mul, sub_ne_zero]
  tauto

/-- Exact local density numerator for distinct nonzero slopes. -/
theorem prime_pattern_pencil_card (S : Finset F) (hS : 0 ∉ S) :
    (linePencilComplement (insert 0 S)).card =
      (Fintype.card F - S.card - 1) * (Fintype.card F - 1) := by
  rw [linePencilComplement_card, card_insert_of_notMem hS, Nat.sub_add_eq]

/-- Union of prescribed affine lines. -/
def forbiddenAffineLines {ι : Type*} (s : Finset ι) (A B C : ι → F) : Finset (F × F) :=
  s.biUnion (fun i => coordinateBoxLine univ univ (A i) (B i) (C i))

/-- Every nondegenerate affine line contributes at most one field-cardinality
to the forbidden set, even when some lines coincide. -/
theorem forbiddenAffineLines_card_le {ι : Type*} (s : Finset ι) (A B C : ι → F)
    (h : ∀ i ∈ s, A i ≠ 0 ∨ B i ≠ 0) :
    (forbiddenAffineLines s A B C).card ≤ s.card * Fintype.card F := by
  refine card_biUnion_le.trans ?_
  calc
    ∑ i ∈ s, (coordinateBoxLine univ univ (A i) (B i) (C i)).card
        ≤ ∑ _i ∈ s, Fintype.card F := by
          apply sum_le_sum
          intro i hi
          simpa only [card_univ, max_self] using
            coordinateBoxLine_card_le_max univ univ (A i) (B i) (C i) (h i hi)
    _ = s.card * Fintype.card F := by simp

/-- Fewer than `|F|` nondegenerate affine lines cannot cover the plane. -/
theorem exists_avoiding_affine_lines {ι : Type*} (s : Finset ι) (A B C : ι → F)
    (h : ∀ i ∈ s, A i ≠ 0 ∨ B i ≠ 0) (hs : s.card < Fintype.card F) :
    ∃ x y : F, ∀ i ∈ s, A i * x + B i * y ≠ C i := by
  have hcard : (forbiddenAffineLines s A B C).card < Fintype.card (F × F) := by
    apply lt_of_le_of_lt (forbiddenAffineLines_card_le s A B C h)
    rw [Fintype.card_prod]
    exact Nat.mul_lt_mul_of_pos_right hs Fintype.card_pos
  have hnonempty : (forbiddenAffineLines s A B C)ᶜ.Nonempty := by
    rw [← card_pos, card_compl]
    exact Nat.sub_pos_of_lt hcard
  obtain ⟨z, hz⟩ := hnonempty
  have hz := mem_compl.mp hz
  refine ⟨z.1, z.2, ?_⟩
  intro i hi heq
  exact hz (mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_univ _, mem_univ _⟩, heq⟩⟩)

/-- Simultaneously avoiding a finite set of values for each linear form
requires fewer than `|F|` form-value pairs. -/
theorem exists_avoiding_linear_values {ι : Type*} (s : Finset ι) (A B : ι → F)
    (T : Finset F) (h : ∀ i ∈ s, A i ≠ 0 ∨ B i ≠ 0)
    (hcard : s.card * T.card < Fintype.card F) :
    ∃ x y : F, ∀ i ∈ s, ∀ c ∈ T, A i * x + B i * y ≠ c := by
  obtain ⟨x, y, hxy⟩ := exists_avoiding_affine_lines (s ×ˢ T)
    (fun j => A j.1) (fun j => B j.1) Prod.snd
    (fun j hj => h j.1 (mem_product.mp hj).1)
    (by simpa only [card_product] using hcard)
  exact ⟨x, y, fun i hi c hc => hxy (i, c) (mem_product.mpr ⟨hi, hc⟩)⟩

/-- Simultaneous exclusions of zero and minus one hold whenever
the field has more than twice as many elements as there are forms. -/
theorem exists_avoiding_zero_neg_one {ι : Type*} (s : Finset ι) (A B : ι → F)
    (h : ∀ i ∈ s, A i ≠ 0 ∨ B i ≠ 0)
    (hcard : 2 * s.card < Fintype.card F) :
    ∃ x y : F, ∀ i ∈ s,
      A i * x + B i * y ≠ 0 ∧ A i * x + B i * y ≠ -1 := by
  have hT : ({0, -1} : Finset F).card = 2 := by simp
  obtain ⟨x, y, hxy⟩ := exists_avoiding_linear_values s A B {0, -1} h
    (by rw [hT, mul_comm]; exact hcard)
  exact ⟨x, y, fun i hi => ⟨hxy i hi 0 (by simp), hxy i hi (-1) (by simp)⟩⟩

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
