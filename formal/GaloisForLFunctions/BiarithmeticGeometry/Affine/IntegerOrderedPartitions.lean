import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteOrderedPartitions
import Mathlib.Data.Int.Interval

/-!
# Integer-interval formulas for ordered partitions

Reversing the preceding indices in an integer interval writes an ordered
weight as a product over positive displacements from the current index.
Factors whose nonconstant part vanishes after multiplication by the leading
cutoff can be removed by truncating that displacement interval.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.FiniteOrderedPartitions
noncomputable section

/-- Earlier indices in an interval correspond exactly to positive displacements. -/
theorem orderedWeight_Icc (l u i : ℤ) (hi : i ≤ u) (a : ℤ → ℝ) :
    orderedWeight (Finset.Icc l u) a i =
      a i * ∏ m ∈ Finset.Icc 1 (i - l), (1 - a (i - m)) := by
  unfold orderedWeight
  congr 1
  apply Finset.prod_bij (fun j _ => i - j)
  · intro j hj
    obtain ⟨hj, hji⟩ := Finset.mem_filter.mp hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  · intro j _ j' _ h
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨i - m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_, ?_⟩, ?_⟩ <;> omega
  · intro j _
    rw [show i - (i - j) = j by omega]

/-- A leading cutoff annihilating all distant factors permits exact finite truncation. -/
theorem mul_prod_Icc_truncate (a : ℝ) (f : ℤ → ℝ) (L B : ℤ)
    (h : ∀ m, B < m → a * f m = 0) :
    a * (∏ m ∈ Finset.Icc 1 L, (1 - f m)) =
      a * ∏ m ∈ Finset.Icc 1 (min L B), (1 - f m) := by
  by_cases ha : a = 0
  · simp only [ha, zero_mul]
  have hs : Finset.Icc 1 (min L B) ⊆ Finset.Icc 1 L := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨hm1, hm2.trans (min_le_left L B)⟩
  have hp : (∏ m ∈ Finset.Icc 1 (min L B), (1 - f m)) =
      ∏ m ∈ Finset.Icc 1 L, (1 - f m) := by
    apply Finset.prod_subset hs
    intro m hm hn
    have hmB : B < m := by
      rw [Finset.mem_Icc] at hm hn
      omega
    have hf : f m = 0 := (mul_eq_zero.mp (h m hmB)).resolve_left ha
    rw [hf, sub_zero]
  rw [hp]

#print axioms orderedWeight_Icc
#print axioms mul_prod_Icc_truncate

end
end GaloisForLFunctions.BiarithmeticGeometry.FiniteOrderedPartitions
