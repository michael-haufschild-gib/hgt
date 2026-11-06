import GaloisForLFunctions.HTGeometry.SymmetricCharacters.FiniteColoring
import Mathlib.GroupTheory.Perm.Fin

/-!
# Cycle values of independent-color characters

A cyclic permutation fixes exactly the constant words. Its character is therefore the power
sum of the color weights. Disjoint-block multiplicativity then gives the cycle-product formula
for every finite list of cycles.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.SymmetricCharacters

variable {A : Type*} [Fintype A]

omit [Fintype A] in
/-- A word invariant under one full cyclic rotation has only one color. -/
theorem fixed_finRotate_iff (n : ℕ) (x : Fin (n + 1) → A) :
    x ∘ finRotate (n + 1) = x ↔ x = fun _ => x 0 := by
  constructor
  · intro h
    funext i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hi := congrFun h i.castSucc
      have hrot : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      change x (finRotate (n + 1) i.castSucc) = x i.castSucc at hi
      rw [hrot] at hi
      exact hi.trans ih
  · intro h
    rw [h]
    rfl

/-- The value on a cycle of length `n+1` is its corresponding color power sum. -/
theorem coloringCharacter_finRotate (w : A → NNReal) (n : ℕ) :
    coloringCharacter w (finRotate (n + 1)) = ∑ a, (w a : ℝ) ^ (n + 1) := by
  classical
  letI : DecidableEq (Fin (n + 1)) := Classical.decEq _
  have hterm (x : Fin (n + 1) → A) :
      (if x ∘ finRotate (n + 1) = x then wordWeight w x else 0) =
        ∑ a, if x = (fun _ => a) then (w a : ℝ) ^ (n + 1) else 0 := by
    rw [Fintype.sum_eq_single (x 0)]
    · simp only [fixed_finRotate_iff]
      split_ifs with hx
      · rw [hx]
        simp [wordWeight]
      · rfl
    · intro a ha
      apply if_neg
      intro hx
      exact ha (congrFun hx 0).symm
  unfold coloringCharacter
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Positions of a finite list of nonempty cycles; each entry is one less than its length. -/
def CyclePositions : List ℕ → Type
  | [] => Empty
  | n :: ns => Fin (n + 1) ⊕ CyclePositions ns

instance cyclePositionsFintype (ns : List ℕ) : Fintype (CyclePositions ns) := by
  induction ns with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons n ns ih => exact @instFintypeSum (Fin (n + 1)) (CyclePositions ns) inferInstance ih

/-- The permutation with the specified cyclic blocks. -/
def cyclePermutation : (ns : List ℕ) → Equiv.Perm (CyclePositions ns)
  | [] => Equiv.refl Empty
  | n :: ns => Equiv.sumCongr (finRotate (n + 1)) (cyclePermutation ns)

/-- The complete product-of-power-sums formula, including cycles of length one. -/
theorem coloringCharacter_cyclePermutation (w : A → NNReal) (ns : List ℕ) :
    coloringCharacter w (cyclePermutation ns) =
      (ns.map fun n => ∑ a, (w a : ℝ) ^ (n + 1)).prod := by
  induction ns with
  | nil =>
    change coloringCharacter w (1 : Equiv.Perm Empty) = 1
    rw [coloringCharacter_one]
    simp
  | cons n ns ih =>
    change coloringCharacter w (Equiv.sumCongr (finRotate (n + 1)) (cyclePermutation ns)) = _
    rw [coloringCharacter_sumCongr, coloringCharacter_finRotate, ih]
    rfl

end GaloisForLFunctions.SymmetricCharacters
