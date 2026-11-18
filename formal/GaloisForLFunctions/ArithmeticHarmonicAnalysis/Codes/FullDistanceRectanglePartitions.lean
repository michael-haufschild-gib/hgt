import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.SeparatedWordBoxes
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Disjoint rectangle partitions at full Hamming distance

The full-distance adjacency matrix has an explicit tensor inverse over the
rationals. Its rank yields the exact partition number for arbitrary finite
products of alphabets.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset Matrix
open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι]

abbrev chartWord (q : ι → ℕ) := ∀ i, Fin (q i + 2)

/-- Rational adjacency matrix for the relation of differing at every site. -/
def distanceMatrix (q : ι → ℕ) : Matrix (chartWord q) (chartWord q) ℚ :=
  of fun x y => ∏ i, if x i = y i then 0 else 1

private theorem distanceMatrix_apply (q : ι → ℕ) (x y : chartWord q) :
    distanceMatrix q x y = if ∀ i, x i ≠ y i then 1 else 0 := by
  change (∏ i, if x i = y i then (0:ℚ) else 1) = _
  split_ifs with h
  · exact prod_eq_one fun i _ => if_neg (h i)
  · push Not at h
    obtain ⟨i,hi⟩ := h
    exact prod_eq_zero (mem_univ i) (if_pos hi)

/-- Tensor product of the one-coordinate complementary adjacency inverses. -/
def distanceInverse (q : ι → ℕ) : Matrix (chartWord q) (chartWord q) ℚ :=
  of fun y z => ∏ i, (((q i:ℚ)+1)⁻¹ - if y i = z i then 1 else 0)

private theorem letter_inverse (n : ℕ) (x z : Fin (n+2)) :
    (∑ y : Fin (n+2), (if x = y then (0:ℚ) else 1) *
      (((n:ℚ)+1)⁻¹ - if y = z then 1 else 0)) = if x = z then 1 else 0 := by
  let c := ((n:ℚ)+1)⁻¹
  let f (y : Fin (n+2)) : ℚ := c - if y = z then 1 else 0
  have hf (y : Fin (n+2)) : (if x = y then (0:ℚ) else 1) * f y =
      f y - (if y = x then f x else 0) := by
    by_cases h : y = x
    · subst y
      simp
    · simp [h,Ne.symm h]
  change (∑ y, (if x = y then (0:ℚ) else 1) * f y) = _
  simp_rw [hf]
  rw [sum_sub_distrib]
  by_cases hx : x = z <;> simp [f,sum_sub_distrib,nsmul_eq_mul,c,hx] <;>
    field_simp [show (n:ℚ)+1 ≠ 0 by positivity] <;> ring

/-- The inverse exists in all dimensions, including heterogeneous alphabets. -/
theorem distanceMatrix_mul_inverse (q : ι → ℕ) : distanceMatrix q * distanceInverse q = 1 := by
  ext x z
  rw [Matrix.mul_apply]
  change (∑ y : chartWord q, (∏ i, if x i = y i then (0:ℚ) else 1) *
    (∏ i, (((q i:ℚ)+1)⁻¹ - if y i = z i then 1 else 0))) = _
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (y : Fin (q i+2)) => (if x i = y then (0:ℚ) else 1) *
    (((q i:ℚ)+1)⁻¹ - if y = z i then 1 else 0))]
  simp_rw [letter_inverse]
  rw [Matrix.one_apply]
  by_cases h : x = z
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact prod_eq_zero (mem_univ i) (if_neg hi)

theorem distanceMatrix_rank (q : ι → ℕ) :
    (distanceMatrix q).rank = ∏ i, (q i + 2) := by
  have hc : Fintype.card (chartWord q) = ∏ i, (q i+2) := by simp [chartWord,Fintype.card_pi]
  have h := Matrix.rank_mul_le_left (distanceMatrix q) (distanceInverse q)
  rw [distanceMatrix_mul_inverse,Matrix.rank_one,hc] at h
  exact le_antisymm ((distanceMatrix q).rank_le_card_width.trans_eq hc) h

/-- A disjoint rectangle representation counts each permitted pair once. -/
def partitionsDistance {q : ι → ℕ} {κ : Type*} [Fintype κ] (L R : κ → Finset (chartWord q)) : Prop :=
  ∀ x y, (univ.filter fun j => x ∈ L j ∧ y ∈ R j).card = if ∀ i, x i ≠ y i then 1 else 0

/-- The rank bound applies even when the rectangle sides have no product structure. -/
theorem disjointDistancePartition_bound {q : ι → ℕ} {κ : Type*} [Fintype κ]
    (L R : κ → Finset (chartWord q)) (h : partitionsDistance L R) :
    ∏ i, (q i+2) ≤ Fintype.card κ := by
  let A : Matrix (chartWord q) κ ℚ := of fun x j => if x ∈ L j then 1 else 0
  let B : Matrix κ (chartWord q) ℚ := of fun j y => if y ∈ R j then 1 else 0
  have he : distanceMatrix q = A * B := by
    ext x y
    rw [distanceMatrix_apply,Matrix.mul_apply]
    have he' (j : κ) : A x j * B j y = if x ∈ L j ∧ y ∈ R j then 1 else 0 := by
      by_cases hl : x ∈ L j <;> by_cases hr : y ∈ R j <;> simp [A,B,hl,hr]
    simp_rw [he']
    have hh := congrArg (Nat.cast : ℕ → ℚ) (h x y)
    simpa [sum_boole] using hh.symm
  rw [← distanceMatrix_rank,he]
  exact (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width

/-- The partition number equals the word count. The construction assigns one rectangle
to each left word, so the lower bound remains sharp with varying alphabet sizes. -/
theorem disjointDistancePartition_number (q : ι → ℕ) :
    IsLeast {k : ℕ | ∃ L R : Fin k → Finset (chartWord q), partitionsDistance L R}
      (∏ i, (q i+2)) := by
  have hc : Fintype.card (chartWord q) = ∏ i, (q i+2) := by simp [chartWord,Fintype.card_pi]
  let e : Fin (∏ i, (q i+2)) ≃ chartWord q := (Fintype.equivFinOfCardEq hc).symm
  constructor
  · refine ⟨fun j => {e j},fun j => oppositeBox {e j},?_⟩
    intro x y
    have he : (univ.filter fun j => x ∈ ({e j} : Finset _) ∧ y ∈ oppositeBox {e j}) =
        if ∀ i, x i ≠ y i then {e.symm x} else ∅ := by
      ext j
      by_cases hj : e j = x
      · subst x
        by_cases hy : ∀ i, e j i ≠ y i <;> simp [hy,mem_oppositeBox]
      · have hn : j ≠ e.symm x := fun h => hj (by rw [h,e.apply_symm_apply])
        have hxj : x ≠ e j := Ne.symm hj
        split_ifs <;> simp [hxj,hn]
    rw [he]
    split_ifs <;> simp
  · rintro k ⟨L,R,h⟩
    simpa using disjointDistancePartition_bound L R h
#print axioms distanceMatrix_mul_inverse
#print axioms distanceMatrix_rank
#print axioms disjointDistancePartition_number

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
