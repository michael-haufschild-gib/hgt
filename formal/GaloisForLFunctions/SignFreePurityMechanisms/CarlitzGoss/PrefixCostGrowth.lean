import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.GreedyOptimality

/-!
# Growth of greedy prefix costs

The proper-prefix cost of a greedy composition is less than twice the
proper-prefix value. Merging the final two parts of a longer composition
and using the half-total bound separates consecutive prefix values.
Optimality then makes consecutive greedy prefix costs more than double.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} {S : Finset (Digit p)}

/-- Total value times the number of parts, minus weighted part value. -/
def prefixCost (C : DigitComposition p s m S) : ℤ := (m : ℤ) * digitValue p S - C.weight

theorem prefixCost_nonneg (C : DigitComposition p s m S) (hp : 0 < p) : 0 ≤ C.prefixCost :=
  sub_nonneg.mpr (C.weight_le hp)

/-- Merging the last two parts preserves admissibility. -/
def mergeLast (C : DigitComposition p s (m + 2) S) : DigitComposition p s (m + 1) S :=
  C.initial.extendLast C.prefix_disjoint_last C.prefix_union_last

theorem mergeLast_last (C : DigitComposition p s (m + 2) S) :
    C.mergeLast.value (Fin.last m) = C.initial.value (Fin.last m) + C.value (Fin.last (m + 1)) :=
  C.initial.extendLast_last C.prefix_disjoint_last C.prefix_union_last

theorem mergeLast_weight (C : DigitComposition p s (m + 2) S) :
    C.mergeLast.weight = C.weight - C.value (Fin.last (m + 1)) := by
  rw [mergeLast, extendLast_weight, C.weight_eq_initial_add_last]
  change C.initial.weight + ((m + 1 : ℕ) : ℤ) * C.value (Fin.last (m + 1)) = _
  push_cast
  ring

/-- Merging the final two parts removes exactly the proper-prefix value from cost. -/
theorem mergeLast_prefixCost (C : DigitComposition p s (m + 2) S) :
    C.mergeLast.prefixCost = C.prefixCost - digitValue p (C.prefixDigits (m + 1)) := by
  have htotal := digitValue_union C.prefix_disjoint_last
  rw [C.prefix_union_last] at htotal
  change digitValue p S = digitValue p (C.prefixDigits (m + 1)) + C.value (Fin.last (m + 1)) at htotal
  rw [prefixCost, prefixCost, C.mergeLast_weight, htotal]
  push_cast
  ring

variable [NeZero s]

/-- A greedy composition's cost is less than twice its proper-prefix value. -/
theorem IsGreedy.prefixCost_lt_twice_prefix {C : DigitComposition p s (m + 2) S}
    (hp : 2 ≤ p) (hC : C.IsGreedy) :
    C.prefixCost < 2 * digitValue p (C.prefixDigits (m + 1)) := by
  have hweight := greedy_weight_lower m hp C.initial hC.initial C.initial_total_divisible
  have htotal := digitValue_union C.prefix_disjoint_last
  rw [C.prefix_union_last] at htotal
  change digitValue p S = digitValue p (C.prefixDigits (m + 1)) + C.value (Fin.last (m + 1)) at htotal
  rw [prefixCost, C.weight_eq_initial_add_last, htotal]
  push_cast
  nlinarith only [hweight]

/-- For a divisible total, the greedy prefix cost is strictly below that total. -/
theorem IsGreedy.prefixCost_lt_total {C : DigitComposition p s (m + 1) S}
    (hp : 2 ≤ p) (hC : C.IsGreedy) (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) :
    C.prefixCost < digitValue p S := by
  cases m with
  | zero =>
    have hval : C.value 0 = digitValue p S := by simpa only [Fin.sum_univ_one] using C.sum_values
    have hweight : C.weight = digitValue p S := by
      simp only [weight, Fin.sum_univ_one, Fin.val_zero, Nat.zero_add, Nat.cast_one, one_mul, hval]
    have hpos := C.value_pos (by omega : 0 < p) 0
    rw [hval] at hpos
    simpa only [prefixCost, Nat.cast_one, one_mul, hweight, sub_self] using hpos
  | succ m =>
    have hcost := hC.prefixCost_lt_twice_prefix hp
    have hhalf := hC.last_gt_half hp hN
    have htotal := digitValue_union C.prefix_disjoint_last
    rw [C.prefix_union_last] at htotal
    change digitValue p S = digitValue p (C.prefixDigits (m + 1)) + C.value (Fin.last (m + 1)) at htotal
    linarith only [hcost, hhalf, htotal]

/-- Consecutive greedy proper-prefix values grow by more than a factor of two. -/
theorem IsGreedy.twice_prefix_lt_next_prefix
    {C : DigitComposition p s (m + 2) S} {D : DigitComposition p s (m + 3) S}
    (hp : 2 ≤ p) (hC : C.IsGreedy) (hD : D.IsGreedy) :
    2 * digitValue p (C.prefixDigits (m + 1)) < digitValue p (D.prefixDigits (m + 2)) := by
  have hhalf := hD.initial.last_gt_half hp D.initial_total_divisible
  have hmax := hC.last_max D.mergeLast
  rw [D.mergeLast_last] at hmax
  have htotalC := digitValue_union C.prefix_disjoint_last
  have htotalD := digitValue_union D.prefix_disjoint_last
  rw [C.prefix_union_last] at htotalC
  rw [D.prefix_union_last] at htotalD
  change digitValue p S = digitValue p (C.prefixDigits (m + 1)) + C.value (Fin.last (m + 1)) at htotalC
  change digitValue p S = digitValue p (D.prefixDigits (m + 2)) + D.value (Fin.last (m + 2)) at htotalD
  linarith only [hhalf, hmax, htotalC, htotalD]

/-- Optimality bounds the next cost increment below by the next proper-prefix value. -/
theorem IsGreedy.next_prefix_le_cost_sub
    {C : DigitComposition p s (m + 2) S} (D : DigitComposition p s (m + 3) S)
    (hp : 2 ≤ p) (hC : C.IsGreedy) :
    digitValue p (D.prefixDigits (m + 2)) ≤ D.prefixCost - C.prefixCost := by
  have ho := hC.isOptimal hp D.mergeLast
  have hc : C.prefixCost ≤ D.mergeLast.prefixCost := by
    unfold prefixCost
    linarith only [ho]
  rw [D.mergeLast_prefixCost] at hc
  linarith only [hc]

/-- Consecutive greedy costs more than double. -/
theorem IsGreedy.twice_prefixCost_lt
    {C : DigitComposition p s (m + 2) S} {D : DigitComposition p s (m + 3) S}
    (hp : 2 ≤ p) (hC : C.IsGreedy) (hD : D.IsGreedy) :
    2 * C.prefixCost < D.prefixCost := by
  have hcost := hC.prefixCost_lt_twice_prefix hp
  have hprefix := hC.twice_prefix_lt_next_prefix hp hD
  have hincrement := hC.next_prefix_le_cost_sub D hp
  linarith only [hcost, hprefix, hincrement]

/-- Three consecutive greedy costs have strictly increasing slopes. The
lowest-degree cost only needs nonnegativity. -/
theorem IsGreedy.prefixCost_strictConvex
    (B : DigitComposition p s (m + 1) S)
    {C : DigitComposition p s (m + 2) S} {D : DigitComposition p s (m + 3) S}
    (hp : 2 ≤ p) (hC : C.IsGreedy) (hD : D.IsGreedy) :
    C.prefixCost - B.prefixCost < D.prefixCost - C.prefixCost := by
  have hdouble := hC.twice_prefixCost_lt hp hD
  have hB := B.prefixCost_nonneg (by omega : 0 < p)
  linarith only [hdouble, hB]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsGreedy.twice_prefixCost_lt
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsGreedy.prefixCost_strictConvex
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsGreedy.prefixCost_lt_total
