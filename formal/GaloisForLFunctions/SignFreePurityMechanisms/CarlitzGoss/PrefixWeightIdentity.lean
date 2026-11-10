import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.InitialCompositions
import Mathlib.Order.Interval.Finset.Nat

/-!
# Weight comparisons through proper prefixes

Each digit in part `i` occurs in exactly `m−i` proper prefixes. Hence the
weighted part sum equals total value times the number of parts minus total
prefix value. This turns a carry modification's prefix costs into its gain.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} {S : Finset (Digit p)}

/-- The weighted sum of parts equals total value times the number of parts,
minus the sum of all proper-prefix values. -/
theorem weight_add_prefix_sum (C : DigitComposition p s (m + 1) S) :
    C.weight + (∑ j ∈ Icc 1 m, digitValue p (C.prefixDigits j)) =
      ((m + 1 : ℕ) : ℤ) * digitValue p S := by
  have hcount (i : Fin (m + 1)) :
      (∑ j ∈ Icc 1 m, if i.val < j then C.value i else 0) =
        ((m - i.val : ℕ) : ℤ) * C.value i := by
    have hfilter : (Icc 1 m).filter (fun j => i.val < j) = Icc (i.val + 1) m := by
      ext j
      simp only [mem_filter, mem_Icc]
      omega
    rw [← sum_filter, hfilter, sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hi : m + 1 - (i.val + 1) = m - i.val := by omega
    rw [hi]
  have hpref : (∑ j ∈ Icc 1 m, digitValue p (C.prefixDigits j)) =
      ∑ i : Fin (m + 1), ((m - i.val : ℕ) : ℤ) * C.value i := by
    simp only [C.value_prefix, sum_filter]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => hcount i
  rw [weight, hpref, ← sum_add_distrib, ← C.sum_values, mul_sum]
  apply sum_congr rfl
  intro i _
  have hi : i.val ≤ m := by have := i.isLt; omega
  rw [Nat.cast_sub hi]
  push_cast
  ring

/-- Weight differences are the reversed differences of all proper-prefix values. -/
theorem weight_sub_eq_prefix_sum (C D : DigitComposition p s (m + 1) S) :
    D.weight - C.weight =
      ∑ j ∈ Icc 1 m, (digitValue p (C.prefixDigits j) - digitValue p (D.prefixDigits j)) := by
  rw [sum_sub_distrib]
  have hC := C.weight_add_prefix_sum
  have hD := D.weight_add_prefix_sum
  linarith only [hC, hD]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.weight_sub_eq_prefix_sum
