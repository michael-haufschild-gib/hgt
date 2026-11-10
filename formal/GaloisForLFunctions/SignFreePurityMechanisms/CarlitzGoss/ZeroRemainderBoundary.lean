import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PrefixCostGrowth

/-!
# The zero-remainder boundary

Appending an empty final part preserves weight and adds the total digit
value to prefix cost. Its proper parts are all divisible exactly when the
total is divisible. Whenever a positive-remainder composition exists, its
greedy weight strictly exceeds every admissible zero-remainder weight.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} {S : Finset (Digit p)}

/-- The actual parts obtained by appending an empty remainder. -/
def zeroRemainderParts (C : DigitComposition p s (m + 1) S) :
    Fin (m + 2) → Finset (Digit p) := Fin.snoc C.parts ∅

def zeroRemainderValue (C : DigitComposition p s (m + 1) S) (i : Fin (m + 2)) : ℤ :=
  digitValue p (C.zeroRemainderParts i)

theorem zeroRemainderValue_eq (C : DigitComposition p s (m + 1) S) :
    C.zeroRemainderValue = Fin.snoc C.value 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [zeroRemainderValue, zeroRemainderParts, Fin.snoc_last, digitValue, tokenValue, sum_empty]
  · simp only [zeroRemainderValue, zeroRemainderParts, Fin.snoc_castSucc, value]

/-- Weighted value of the composition with an empty final remainder. -/
def zeroRemainderWeight (C : DigitComposition p s (m + 1) S) : ℤ :=
  ∑ i : Fin (m + 2), ((i.val + 1 : ℕ) : ℤ) * C.zeroRemainderValue i

theorem zeroRemainderWeight_eq (C : DigitComposition p s (m + 1) S) :
    C.zeroRemainderWeight = C.weight := by
  rw [zeroRemainderWeight, C.zeroRemainderValue_eq, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, mul_zero, add_zero]
  rfl

/-- The empty-remainder extension has divisible proper parts exactly when
the original total is divisible. -/
theorem zeroRemainder_proper_divisible_iff (C : DigitComposition p s (m + 1) S) :
    (∀ i : Fin (m + 1), ((p : ℤ) ^ s - 1) ∣ digitValue p (C.zeroRemainderParts i.castSucc)) ↔
      ((p : ℤ) ^ s - 1) ∣ digitValue p S := by
  change (∀ i, ((p : ℤ) ^ s - 1) ∣ C.value i) ↔ _
  constructor
  · intro h
    rw [← C.sum_values]
    exact dvd_sum fun i _ => h i
  · exact C.all_divisible_of_total

/-- Prefix cost after appending an empty remainder. -/
def zeroRemainderCost (C : DigitComposition p s (m + 1) S) : ℤ :=
  ((m + 2 : ℕ) : ℤ) * digitValue p S - C.zeroRemainderWeight

theorem zeroRemainderCost_eq (C : DigitComposition p s (m + 1) S) :
    C.zeroRemainderCost = C.prefixCost + digitValue p S := by
  rw [zeroRemainderCost, C.zeroRemainderWeight_eq, prefixCost]
  push_cast
  ring

/-- The final zero-remainder cost increment is exactly the total value. -/
theorem zeroRemainderCost_sub (C : DigitComposition p s (m + 1) S) :
    C.zeroRemainderCost - C.prefixCost = digitValue p S := by
  rw [C.zeroRemainderCost_eq]
  ring

variable [NeZero s]

/-- Every positive-remainder greedy composition outweighs every admissible
zero-remainder extension on the same digits. -/
theorem IsGreedy.zeroRemainderWeight_lt {G : DigitComposition p s (m + 2) S}
    (hp : 2 ≤ p) (hG : G.IsGreedy) (C : DigitComposition p s (m + 1) S)
    (hdiv : ∀ i : Fin (m + 1),
      ((p : ℤ) ^ s - 1) ∣ digitValue p (C.zeroRemainderParts i.castSucc)) :
    C.zeroRemainderWeight < G.weight := by
  have hN := C.zeroRemainder_proper_divisible_iff.mp hdiv
  have hlow := greedy_weight_lower (m + 1) hp G hG hN
  rw [C.zeroRemainderWeight_eq]
  exact (C.weight_le (by omega : 0 < p)).trans_lt hlow

/-- At a divisible endpoint, the zero-remainder cost more than doubles the
preceding greedy cost, so the endpoint slope is strictly larger too. -/
theorem IsGreedy.twice_prefixCost_lt_zeroRemainderCost
    {C : DigitComposition p s (m + 1) S} (hp : 2 ≤ p) (hC : C.IsGreedy)
    (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) :
    2 * C.prefixCost < C.zeroRemainderCost := by
  have hcost := hC.prefixCost_lt_total hp hN
  rw [C.zeroRemainderCost_eq]
  linarith only [hcost]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
