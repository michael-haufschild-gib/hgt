/-
The across-class sum through an exponent pair, and the target it names.

The across-class object is `Σ_(d ≤ D) e(β√d)` with `β ≍ N`, `D ≍ N^(2/3)`.  Its derivatives satisfy
`f^(k)(d) ≍ β/d^(k-1/2)`, and `F := D·|f'| ≍ β√D = N^(4/3)`, so `f^(k) ≍ F/D^k` exactly: **the phase is
a model phase**, and an exponent pair applies with

    (F/D)^κ D^λ = (N^(2/3))^κ (N^(2/3))^λ = **N^(2(κ+λ)/3)** .

So the saving over the trivial bound `N^(2/3)` is

    **2(1 - κ - λ)/3** ,

two thirds of the pair's own distance from `κ + λ = 1`.  Weyl's pair `κ+λ = 5/6` gives `N^(5/9)`,
reproducing the third-derivative test exactly; Bourgain's `κ+λ = 17/21` gives **`N^(34/63)`**, better by
`1/63`, with saving `8/63`.

Condition (ii) requires a saving of `1/6`, i.e. `2(1-κ-λ)/3 = 1/6`, i.e.

    **κ + λ ≤ 3/4** ,   equivalently   **μ ≤ 1/8** .

The record is `κ+λ = 17/21`, i.e. `μ = 13/84`, so the requirement is `5/168` away in `μ`.  That places
condition (ii) between the record and the campaign's earlier target `μ ≤ 1/12`:

    **13/84 = 0.154762  >  1/8 = 0.125  >  1/12 = 0.083333  >  0** ,

so **condition (ii) is the easiest named target the campaign has produced**.
-/
import GaloisForLFunctions.HTGeometry.AcrossClassDerivativeTests

namespace HTGeometry

/-! ### The exponent-pair bound on the across-class sum -/

/-- Exponent of the across-class bound delivered by a pair with `κ + λ = s`. -/
def acrossPairBound (s : ℚ) : ℚ := 2 * s / 3

/-- **Weyl's pair reproduces the third-derivative test.** -/
theorem weyl_reproduces_third_test : acrossPairBound (5 / 6) = thirdTestBound := by
  rw [thirdTestBound_eq]; unfold acrossPairBound; norm_num

/-- **Bourgain's pair does better.** -/
theorem bourgain_across_bound : acrossPairBound (17 / 21) = 34 / 63 := by
  unfold acrossPairBound; norm_num

/-- **By exactly `1/63`.** -/
theorem bourgain_beats_third_test :
    thirdTestBound - acrossPairBound (17 / 21) = 1 / 63 := by
  rw [thirdTestBound_eq, bourgain_across_bound]; norm_num

/-- The saving over the trivial bound. -/
def acrossPairSaving (s : ℚ) : ℚ := acrossRangeExponent - acrossPairBound s

/-- **It is two thirds of the pair's distance from `κ + λ = 1`.** -/
theorem acrossPairSaving_eq (s : ℚ) : acrossPairSaving s = 2 * (1 - s) / 3 := by
  unfold acrossPairSaving acrossPairBound acrossRangeExponent; ring

/-- **Bourgain's saving is `8/63`.** -/
theorem bourgainAcrossSaving : acrossPairSaving (17 / 21) = 8 / 63 := by
  rw [acrossPairSaving_eq]; norm_num

/-- **Weyl's is `1/9 = 7/63`.** -/
theorem weylAcrossSaving : acrossPairSaving (5 / 6) = 1 / 9 := by
  rw [acrossPairSaving_eq]; norm_num

/-! ### The requirement -/

/-- The value of `κ + λ` at which condition (ii) is met. -/
def conditionTwoSum : ℚ := 3 / 4

/-- **It is exactly where the saving reaches `1/6`.** -/
theorem conditionTwoSum_meets_requirement :
    acrossPairSaving conditionTwoSum = conditionTwoRequirement := by
  rw [acrossPairSaving_eq]
  unfold conditionTwoSum conditionTwoRequirement; norm_num

/-- **In pointwise terms the requirement is `μ ≤ 1/8`.** -/
theorem conditionTwo_mu : (conditionTwoSum - 1 / 2) / 2 = 1 / 8 := by
  unfold conditionTwoSum; norm_num

/-- **The record's sum is `17/21`, i.e. `μ = 13/84`.** -/
theorem record_sum_and_mu :
    (17 / 21 : ℚ) - 1 / 2 = 13 / 42 ∧ ((17 / 21 : ℚ) - 1 / 2) / 2 = bourgainTheta := by
  constructor
  · norm_num
  · unfold bourgainTheta; norm_num

/-- **The gap to the requirement, in `μ`.** -/
theorem gap_to_conditionTwo : bourgainTheta - 1 / 8 = 5 / 168 := by
  unfold bourgainTheta; norm_num

/-- **And in `κ + λ`.** -/
theorem gap_in_sum : (17 / 21 : ℚ) - conditionTwoSum = 5 / 84 := by
  unfold conditionTwoSum; norm_num

/-! ### The ordering of the campaign's targets -/

/-- The campaign's earlier target from the Farey-numerator bound. -/
def fareyTargetMu : ℚ := 1 / 12

/-- **The targets in order: record, condition (ii), Farey, Lindelöf.** -/
theorem target_ordering :
    fareyTargetMu < 1 / 8 ∧ (1 : ℚ) / 8 < bourgainTheta ∧ (0 : ℚ) < fareyTargetMu := by
  unfold fareyTargetMu bourgainTheta
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Condition (ii) is the easiest named target**, closer to the record than the Farey target is. -/
theorem conditionTwo_is_easiest :
    bourgainTheta - 1 / 8 < bourgainTheta - fareyTargetMu ∧
      bourgainTheta - 1 / 8 = 5 / 168 ∧
      bourgainTheta - fareyTargetMu = 1 / 14 := by
  refine ⟨?_, gap_to_conditionTwo, ?_⟩
  · unfold fareyTargetMu bourgainTheta; norm_num
  · unfold fareyTargetMu bourgainTheta; norm_num

/-- **Status of condition (ii).**  Bourgain's pair supplies `8/63` of the required `1/6`; the fraction
in hand is `16/21`, and the shortfall is `5/126`. -/
theorem conditionTwo_status :
    acrossPairSaving (17 / 21) = 8 / 63 ∧
      (8 / 63 : ℚ) / conditionTwoRequirement = 16 / 21 ∧
      conditionTwoRequirement - 8 / 63 = 5 / 126 := by
  refine ⟨bourgainAcrossSaving, ?_, ?_⟩
  · unfold conditionTwoRequirement; norm_num
  · unfold conditionTwoRequirement; norm_num

end HTGeometry
