import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeQuadraticDiscriminant
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeVertexSignedLocalization
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Set.Card

/-!
# Real orientation fibres of the prime-quadratic arithmetic family

The actual real solutions of the integral equation `y²=disc(F_n)` form a
finite set. Repeated prime factors give one branch point; otherwise the
discriminant gives zero or two real orientations. The disjoint union through
an integer cutoff recovers the original signed local-index sum.
-/

noncomputable section
open Finset Polynomial ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

/-- Real points of an integral quadratic cover. -/
def realQuadraticRootSet (d : ℤ) : Set ℝ := {y | y ^ 2 = (d : ℝ)}

/-- The equation itself determines all its real solutions. -/
theorem realQuadraticRootSet_eq (d : ℤ) :
    realQuadraticRootSet d =
      if d < 0 then ∅ else {Real.sqrt d, -Real.sqrt d} := by
  by_cases hd : d < 0
  · rw [if_pos hd]
    ext y
    have hd' : (d : ℝ) < 0 := by exact_mod_cast hd
    simp only [realQuadraticRootSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hy
    nlinarith [sq_nonneg y]
  · rw [if_neg hd]
    have hd' : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_not_gt hd
    ext y
    simp only [realQuadraticRootSet, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    calc
      y ^ 2 = (d : ℝ) ↔ y ^ 2 = (Real.sqrt d) ^ 2 := by rw [Real.sq_sqrt hd']
      _ ↔ y = Real.sqrt d ∨ y = -Real.sqrt d := sq_eq_sq_iff_eq_or_eq_neg

theorem realQuadraticRootSet_finite (d : ℤ) : (realQuadraticRootSet d).Finite := by
  rw [realQuadraticRootSet_eq]
  split_ifs <;> simp

noncomputable instance realQuadraticRootSetFintype (d : ℤ) : Fintype (realQuadraticRootSet d) :=
  (realQuadraticRootSet_finite d).fintype

/-- The count includes the single real branch point at zero discriminant. -/
theorem realQuadraticRootSet_card (d : ℤ) :
    (Nat.card (realQuadraticRootSet d) : ℤ) = 1 + d.sign := by
  rw [Nat.card_coe_set_eq, realQuadraticRootSet_eq]
  rcases lt_trichotomy d 0 with hd | rfl | hd
  · rw [if_pos hd, Set.ncard_empty, Int.sign_eq_neg_one_of_neg hd]
    rfl
  · simp
  · have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
    have hs : Real.sqrt d ≠ -Real.sqrt d := by
      have hp := Real.sqrt_pos.mpr hd'
      linarith
    rw [if_neg (not_lt.mpr hd.le), Set.ncard_pair hs, Int.sign_eq_one_of_pos hd]
    rfl

/-- The integral discriminant cover has exactly the required real orientation defect. -/
theorem primeQuadraticOrientation_card {n : ℕ} (hn : n ≠ 0) :
    (Nat.card (realQuadraticRootSet (primeQuadraticPolynomial n).discr) : ℤ) =
      1 + moebius n := by
  rw [realQuadraticRootSet_card, primeQuadraticPolynomial_discr_sign hn]

/-- The actual disjoint union of real arithmetic fibres through a conductor cutoff. -/
abbrev PrimeQuadraticOrientationWindow (N : ℕ) :=
  (n : Icc 1 N) × realQuadraticRootSet (primeQuadraticPolynomial n.val).discr

/-- Cardinality of the disjoint union, defined before its Möbius comparison. -/
def primeQuadraticOrientationCount (N : ℕ) : ℕ :=
  Nat.card (PrimeQuadraticOrientationWindow N)

/-- The centred real count is the integer Möbius sum. -/
theorem primeQuadraticOrientationCount_eq (N : ℕ) :
    (primeQuadraticOrientationCount N : ℤ) =
      N + ∑ n ∈ Icc 1 N, moebius n := by
  classical
  simp only [primeQuadraticOrientationCount, Nat.card_eq_fintype_card, Fintype.card_sigma,
    Nat.cast_sum]
  have h (n : Icc 1 N) :
      (Fintype.card (realQuadraticRootSet (primeQuadraticPolynomial n.val).discr) : ℤ) =
        1 + moebius n.val := by
    rw [← Nat.card_eq_fintype_card]
    exact primeQuadraticOrientation_card (by have := (mem_Icc.mp n.property).1; omega)
  simp_rw [h]
  rw [Finset.sum_coe_sort (Icc 1 N) (fun n => (1 : ℤ) + moebius n),
    Finset.sum_add_distrib]
  simp

/-- Signed relative local indices are the exact defect of the independent real fibre count. -/
theorem primeQuadraticOrientationCount_localIndices (N : ℕ) (hN : 1 ≤ N) :
    (∑ p, primeVertexRelativeIndex N N p) =
      (N : ℤ) + 1 - primeQuadraticOrientationCount N := by
  rw [primeVertexRelativeIndex_sum_mertens N N le_rfl hN,
    primeQuadraticOrientationCount_eq]
  ring

#print axioms realQuadraticRootSet_finite
#print axioms realQuadraticRootSet_card
#print axioms primeQuadraticOrientation_card
#print axioms primeQuadraticOrientationCount_eq
#print axioms primeQuadraticOrientationCount_localIndices

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
