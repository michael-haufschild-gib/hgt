/-
The across-class direction: the second-derivative test is exactly vacuous, the third is not.

Condition (ii) concerns cancellation in the sum over squarefree kernels.  Interchanging the order of
summation, the relevant one-dimensional object is

    Σ_(d ≤ D) e(β √d) ,   with   β ≍ N ,   D ≍ N^(2/3) .

Its derivatives are `f^(k)(d) ≍ β / d^(k - 1/2)`, so the `k`-th derivative parameter has exponent

    **λ_k = 1 - (k - 1/2)·(2/3)** ,

giving `λ_2 = 0` and `λ_3 = -2/3`.

* At `k = 2` the parameter is exactly `1`: **the second-derivative test sits precisely on its own
  boundary and is vacuous** — one more appearance of the critical point the whole problem occupies.
* At `k = 3` the parameter is `N^(-2/3)`, and van der Corput's third-derivative test gives

      max( D + λ₃/6 , D/2 - λ₃/6 ) = max( 5/9 , 4/9 ) = **5/9** ,

  against the trivial `2/3`.  **A saving of `1/9`** — the campaign's first nontrivial estimate in the
  across-class direction.

The saving is not yet enough: condition (ii) requires square-root cancellation across the classes,
worth `1/6`.  But `1/9 > 0`, and the direction is no longer untouched.
-/
import GaloisForLFunctions.HTGeometry.TwoConditionReduction

namespace HTGeometry

/-! ### The derivative parameters -/

/-- Exponent of the phase size `β ≍ N` in the across-class sum. -/
def acrossPhaseExponent : ℚ := 1

/-- Exponent of the summation range `D ≍ N^(2/3)`. -/
def acrossRangeExponent : ℚ := 2 / 3

/-- Exponent of the `k`-th derivative parameter `λ_k ≍ β / D^(k - 1/2)`. -/
def acrossDerivExponent (k : ℚ) : ℚ :=
  acrossPhaseExponent - (k - 1 / 2) * acrossRangeExponent

/-- **At `k = 2` the parameter is exactly `1`.** -/
@[simp] theorem acrossDeriv_second : acrossDerivExponent 2 = 0 := by
  unfold acrossDerivExponent acrossPhaseExponent acrossRangeExponent; norm_num

/-- **At `k = 3` it is `N^(-2/3)`.** -/
@[simp] theorem acrossDeriv_third : acrossDerivExponent 3 = -(2 / 3) := by
  unfold acrossDerivExponent acrossPhaseExponent acrossRangeExponent; norm_num

/-- The parameter decreases with the order. -/
theorem acrossDeriv_antitone {k k' : ℚ} (h : k < k') :
    acrossDerivExponent k' < acrossDerivExponent k := by
  unfold acrossDerivExponent acrossRangeExponent; linarith

/-- **The second-derivative test is vacuous exactly because its parameter is `1`.**  The test needs
`λ < 1`, i.e. a negative exponent. -/
theorem second_test_vacuous : acrossDerivExponent 2 = 0 ∧ ¬ (acrossDerivExponent 2 < 0) := by
  refine ⟨acrossDeriv_second, ?_⟩
  rw [acrossDeriv_second]
  norm_num

/-- **The third-derivative test is not.** -/
theorem third_test_available : acrossDerivExponent 3 < 0 := by
  rw [acrossDeriv_third]; norm_num

/-! ### The third-derivative bound -/

/-- First branch of the third-derivative test: `D · λ₃^(1/6)`. -/
def thirdTestFirst : ℚ := acrossRangeExponent + acrossDerivExponent 3 / 6

/-- Second branch: `D^(1/2) · λ₃^(-1/6)`. -/
def thirdTestSecond : ℚ := acrossRangeExponent / 2 - acrossDerivExponent 3 / 6

/-- **The two branches are `5/9` and `4/9`.** -/
theorem thirdTest_branches : thirdTestFirst = 5 / 9 ∧ thirdTestSecond = 4 / 9 := by
  constructor
  · unfold thirdTestFirst acrossRangeExponent; rw [acrossDeriv_third]; norm_num
  · unfold thirdTestSecond acrossRangeExponent; rw [acrossDeriv_third]; norm_num

/-- The bound is the larger branch. -/
def thirdTestBound : ℚ := max thirdTestFirst thirdTestSecond

/-- **It is `5/9`.** -/
@[simp] theorem thirdTestBound_eq : thirdTestBound = 5 / 9 := by
  unfold thirdTestBound
  rw [thirdTest_branches.1, thirdTest_branches.2]
  norm_num

/-- **And it beats the trivial bound by `1/9`.** -/
theorem thirdTest_nontrivial :
    thirdTestBound < acrossRangeExponent ∧ acrossRangeExponent - thirdTestBound = 1 / 9 := by
  rw [thirdTestBound_eq]
  unfold acrossRangeExponent
  constructor <;> norm_num

/-! ### What condition (ii) still needs -/

/-- The saving condition (ii) requires: square-root cancellation across the classes. -/
def conditionTwoRequirement : ℚ := 1 / 6

/-- **The third-derivative test supplies `1/9` of the required `1/6`.** -/
theorem third_test_partial :
    acrossRangeExponent - thirdTestBound = 1 / 9 ∧
      (1 : ℚ) / 9 < conditionTwoRequirement ∧
      conditionTwoRequirement - 1 / 9 = 1 / 18 := by
  refine ⟨thirdTest_nontrivial.2, ?_, ?_⟩
  · unfold conditionTwoRequirement; norm_num
  · unfold conditionTwoRequirement; norm_num

/-- **The fraction of condition (ii) supplied.** -/
theorem third_test_fraction : ((1 : ℚ) / 9) / conditionTwoRequirement = 2 / 3 := by
  unfold conditionTwoRequirement; norm_num

/-- **Summary.**  The across-class direction is no longer untouched: the second-derivative test is
exactly on its boundary, the third gives a genuine `1/9`, and condition (ii) needs `1/6` — so two
thirds of it is now in hand. -/
theorem across_class_status :
    acrossDerivExponent 2 = 0 ∧
      thirdTestBound = 5 / 9 ∧
      acrossRangeExponent - thirdTestBound = 1 / 9 ∧
      ((1 : ℚ) / 9) / conditionTwoRequirement = 2 / 3 :=
  ⟨acrossDeriv_second, thirdTestBound_eq, thirdTest_nontrivial.2, third_test_fraction⟩

end HTGeometry
