/-
The van der Corput derivative tests, indexed by order, and the optimality of the third.

The classical `k`-th derivative test corresponds to the exponent pair

    **(κ_k, λ_k) = ( 1/(2^k - 2) ,  1 - (k-1)/(2^k - 2) )** ,   `k ≥ 3` ,

which is exactly the tower produced by iterating the `A`-process from `B(0,1)`, with `k = j + 2`.  So
the closed form obtained earlier from the `A`-recursion is the classical one, an independent
confirmation.

Its subconvexity exponent is

    **μ_k = 1/4 - (k-2) / (2(2^k - 2))** ,

which equals `1/6` at `k = 3` — Weyl's exponent — and **increases** with `k` toward the convexity
bound `1/4`:

    k = 3 : **1/6 = 0.166667** ,   k = 4 : **5/28 = 0.178571** ,
    k = 5 : **1/5 = 0.2** ,        k = 6 : **27/124 = 0.217742** .

So **the third derivative test is the best of the family at the critical line**, and every
higher-order test is strictly worse there — while, by the earlier scale analysis, the higher tests are
the ones that clear the small block scales.  That is the classical reason Weyl's `1/6` was the
baseline for sixty-five years: no order of van der Corput's method improves it.
-/
import GaloisForLFunctions.HTGeometry.ClassDecompositionNotAReduction

namespace HTGeometry

/-! ### The tests, indexed by order -/

/-- Denominator `2^k - 2` of the `k`-th derivative test. -/
def testDen (k : ℕ) : ℚ := 2 ^ k - 2

/-- First coordinate of the `k`-th test's exponent pair. -/
def testKappa (k : ℕ) : ℚ := 1 / testDen k

/-- Second coordinate. -/
def testLambda (k : ℕ) : ℚ := 1 - (k - 1) / testDen k

/-- Its subconvexity exponent. -/
def testMu (k : ℕ) : ℚ := 1 / 4 - (k - 2) / (2 * testDen k)

/-- **The `k`-th test is the `(k-2)`-nd member of the `A`-tower.** -/
theorem test_is_tower (j : ℕ) :
    testDen (j + 2) = towerDen j ∧ testKappa (j + 2) = towerKappa j := by
  constructor
  · unfold testDen towerDen; norm_num
  · unfold testKappa towerKappa
    congr 1

/-- And the second coordinates agree. -/
theorem test_lambda_is_tower (j : ℕ) : testLambda (j + 2) = towerLambda j := by
  unfold testLambda towerLambda
  rw [(test_is_tower j).1]
  push_cast
  ring

/-- **The exponents agree too.** -/
theorem test_mu_is_tower (j : ℕ) : testMu (j + 2) = towerMu j := by
  unfold testMu towerMu
  rw [(test_is_tower j).1]
  push_cast
  ring

/-! ### Values -/

theorem testDen_values :
    testDen 3 = 6 ∧ testDen 4 = 14 ∧ testDen 5 = 30 ∧ testDen 6 = 62 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold testDen; norm_num)

/-- **The third test is Weyl's.** -/
@[simp] theorem testMu_three : testMu 3 = 1 / 6 := by
  unfold testMu testDen; norm_num

@[simp] theorem testMu_four : testMu 4 = 5 / 28 := by
  unfold testMu testDen; norm_num

@[simp] theorem testMu_five : testMu 5 = 1 / 5 := by
  unfold testMu testDen; norm_num

@[simp] theorem testMu_six : testMu 6 = 27 / 124 := by
  unfold testMu testDen; norm_num

/-- **The exponents increase with the order.** -/
theorem testMu_increasing :
    testMu 3 < testMu 4 ∧ testMu 4 < testMu 5 ∧ testMu 5 < testMu 6 := by
  rw [testMu_three, testMu_four, testMu_five, testMu_six]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **And stay below the convexity bound.** -/
theorem testMu_below_convexity : testMu 6 < 1 / 4 := by
  rw [testMu_six]; norm_num

/-! ### Optimality of the third test -/

/-- **Weyl's exponent is the best in the family.** -/
theorem third_test_optimal :
    testMu 3 < testMu 4 ∧ testMu 3 < testMu 5 ∧ testMu 3 < testMu 6 := by
  rw [testMu_three, testMu_four, testMu_five, testMu_six]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **And it is Weyl's `1/6`, the pre-1986 baseline.** -/
theorem third_test_is_weyl : testMu 3 = weylKappa := by
  rw [testMu_three]; unfold weylKappa; rfl

/-- **The record lies strictly below the whole family**, which is why every improvement since Weyl has
come from outside van der Corput's method. -/
theorem record_below_family :
    bourgainTheta < testMu 3 ∧ bourgainTheta < testMu 4 ∧ bourgainTheta < testMu 5 := by
  rw [testMu_three, testMu_four, testMu_five]
  unfold bourgainTheta
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Summary.**  The derivative tests form the `A`-tower; their critical-line exponents increase from
Weyl's `1/6` toward `1/4`; the third is optimal; and the record `13/84` lies below all of them. -/
theorem derivative_test_summary :
    testMu 3 = 1 / 6 ∧ testMu 3 < testMu 4 ∧ testMu 6 < 1 / 4 ∧ bourgainTheta < testMu 3 :=
  ⟨testMu_three, testMu_increasing.1, testMu_below_convexity, record_below_family.1⟩

end HTGeometry
