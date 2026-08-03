import Mathlib

/-!
# Ordered set partitions and ordered Bell enumeration

`OrderedPartitionCode n j` is a recursive, proof-relevant encoding of an ordered partition of
`Fin n` into `j` nonempty blocks.  Adding the newest label either inserts it into one of the
existing blocks or creates a singleton in one of the available ordered positions.  The recursion
gives an exact cardinal proof `j! S(n,j)`.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

open scoped BigOperators

/-- Recursive code for an ordered partition of `n` labels into `j` nonempty ordered blocks. -/
def OrderedPartitionCode : ℕ → ℕ → Type
  | 0, 0 => PUnit
  | 0, _ + 1 => PEmpty
  | _ + 1, 0 => PEmpty
  | n + 1, j + 1 =>
      (Fin (j + 1) × OrderedPartitionCode n (j + 1)) ⊕
        (Fin (j + 1) × OrderedPartitionCode n j)

/-- Ordered partition codes are finite. -/
theorem OrderedPartitionCode.finite : ∀ n j, Finite (OrderedPartitionCode n j) := by
  intro n
  induction n with
  | zero =>
      intro j
      cases j <;> simp only [OrderedPartitionCode] <;> infer_instance
  | succ n ih =>
      intro j
      cases j with
      | zero => simp only [OrderedPartitionCode]; infer_instance
      | succ j =>
          simp only [OrderedPartitionCode]
          letI : Finite (OrderedPartitionCode n (j + 1)) := ih (j + 1)
          letI : Finite (OrderedPartitionCode n j) := ih j
          infer_instance

attribute [local instance] OrderedPartitionCode.finite

/-- Exact cardinality of ordered partitions with fixed number of blocks. -/
theorem OrderedPartitionCode.card (n j : ℕ) :
    Nat.card (OrderedPartitionCode n j) = j.factorial * Nat.stirlingSecond n j := by
  induction n generalizing j with
  | zero =>
      cases j with
      | zero => simp [OrderedPartitionCode, Nat.stirlingSecond]
      | succ j => simp [OrderedPartitionCode, Nat.stirlingSecond]
  | succ n ih =>
      cases j with
      | zero => simp [OrderedPartitionCode, Nat.stirlingSecond]
      | succ j =>
          rw [OrderedPartitionCode]
          rw [Nat.card_sum, Nat.card_prod, Nat.card_prod,
            ih (j + 1), ih j, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
          simp only [Nat.card_fin]
          ring

/-- All ordered partitions of `n`, with the number of blocks retained in the sigma index. -/
def OrderedSetPartition (n : ℕ) : Type :=
  Σ j : Fin (n + 1), OrderedPartitionCode n j

instance (n : ℕ) : Finite (OrderedSetPartition n) := by
  unfold OrderedSetPartition
  infer_instance

/-- Ordered Bell formula including the harmless zero-block term. -/
theorem orderedSetPartition_card (n : ℕ) :
    Nat.card (OrderedSetPartition n) =
      ∑ j ∈ Finset.range (n + 1), j.factorial * Nat.stirlingSecond n j := by
  rw [OrderedSetPartition, Nat.card_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun j => Nat.card (OrderedPartitionCode n j)) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  exact OrderedPartitionCode.card n j

/-- For a nonempty label set, the zero-block term vanishes, yielding the standard ordered-Bell
sum from one through `n`. -/
theorem orderedSetPartition_card_eq_Icc (n : ℕ) (hn : 0 < n) :
    Nat.card (OrderedSetPartition n) =
      ∑ j ∈ Finset.Icc 1 n, j.factorial * Nat.stirlingSecond n j := by
  rw [orderedSetPartition_card]
  symm
  apply Finset.sum_subset
  · intro j hj
    have hjle : j ≤ n := (Finset.mem_Icc.mp hj).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hjle)
  · intro j hjRange hjIcc
    have hjlt : j < n + 1 := Finset.mem_range.mp hjRange
    have hjzero : j = 0 := by
      by_contra hjne
      apply hjIcc
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hjne, by omega⟩
    subst j
    cases n with
    | zero => omega
    | succ n => simp [Nat.stirlingSecond]

end IrregularStokes
end GaloisForLFunctions
