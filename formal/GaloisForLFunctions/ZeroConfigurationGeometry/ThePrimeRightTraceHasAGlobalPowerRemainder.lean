import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimeErrorHasAPowerSavingRightTrace
import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripTraceIsContinuous

/-!
# A globally bounded remainder after the right-substrip prime trace

The finite initial interval costs a finite prime prefix and the summable
reciprocal zero mass. Thus the power-saving remainder can be bounded on
the entire half-line where weighted Abel integration takes place.
-/

noncomputable section

open Complex Set MeasureTheory Finset
open _root_.RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- The prime error after its complete right-substrip trace is removed. -/
def primeRightTraceRemainder (σ β x : ℝ) : ℝ :=
  Chebyshev.psi x - x + x ^ β * (rightNormalizedZeroTrace σ β x).re

/-- The continuous zero trace and measurable prime staircase give the
local measurability needed by Abel integration. -/
theorem aestronglyMeasurable_primeRightTraceRemainder
    {σ β : ℝ} (hσ : 1 / 2 < σ)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    AEStronglyMeasurable (primeRightTraceRemainder σ β) (volume.restrict (Ici 1)) := by
  have hψ : Measurable Chebyshev.psi := by
    have hh : Measurable (fun x : ℝ =>
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) :=
      (measurable_from_nat (f := fun N : ℕ =>
        ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n)).comp Nat.measurable_floor
    simpa only [Function.comp_def, ← Chebyshev.psi_eq_sum_Icc] using hh
  have htrace : AEStronglyMeasurable (rightNormalizedZeroTrace σ β)
      (volume.restrict (Ici 1)) :=
    (continuousOn_rightNormalizedZeroTrace hσ hβ).aestronglyMeasurable measurableSet_Ici
  exact (hψ.aestronglyMeasurable.sub measurable_id.aestronglyMeasurable).add
    ((measurable_id.pow_const β).aestronglyMeasurable.mul htrace.re)

/-- The right-trace remainder has a power envelope on all of `[1,∞)`,
with exponent strictly between the retained substrip and its upper bound. -/
theorem exists_global_power_bound_primeRightTraceRemainder {σ β : ℝ}
    (hσ : 1 / 2 < σ) (hσβ : σ < β) (hβ1 : β ≤ 1)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    ∃ κ C : ℝ, σ < κ ∧ κ < β ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |primeRightTraceRemainder σ β x| ≤ C * x ^ κ := by
  obtain ⟨κ, C, x₀, hσκ, hκβ, hC, hb⟩ :=
    exists_power_bound_primeError_add_rightTrace hσ hσβ hβ1 hβ
  let Y := max x₀ 1
  have hY1 : 1 ≤ Y := le_max_right _ _
  have hY0 : 0 ≤ Y := zero_le_one.trans hY1
  let S := ∑' q, rightSubstripTailWeight σ ∅ q
  have hS : 0 ≤ S := tsum_nonneg (rightSubstripTailWeight_nonneg σ ∅)
  let P := ∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, |ArithmeticFunction.vonMangoldt n|
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let B := P + Y + Y ^ β * S
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hκ : 0 ≤ κ := by linarith only [hσ, hσκ]
  have hβ0 : 0 ≤ β := by linarith only [hσ, hσβ]
  refine ⟨κ, C + B, hσκ, hκβ, add_nonneg hC hB, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxκ : 1 ≤ x ^ κ := Real.one_le_rpow hx hκ
  by_cases hYx : Y ≤ x
  · exact (hb x ((le_max_left _ _).trans hYx)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (Real.rpow_nonneg hx0 _))
  · have hxY : x ≤ Y := (lt_of_not_ge hYx).le
    have hψ : |Chebyshev.psi x| ≤ P := by
      rw [Chebyshev.psi_eq_sum_Icc]
      apply (abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn0, hnN⟩ := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨hn0, hnN.trans (Nat.floor_mono hxY)⟩
      · intro n _ _
        exact abs_nonneg _
    have htrace : ‖rightNormalizedZeroTrace σ β x‖ ≤ S := by
      simpa only [Finset.sum_empty, sub_zero] using
        norm_rightNormalizedZeroTrace_sub_sum_le hσ hx hβ ∅
    have htrace' : |x ^ β * (rightNormalizedZeroTrace σ β x).re| ≤ Y ^ β * S := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0 _)]
      exact mul_le_mul (Real.rpow_le_rpow hx0 hxY hβ0)
        ((Complex.abs_re_le_norm _).trans htrace) (abs_nonneg _) (Real.rpow_nonneg hY0 _)
    have hbound : |primeRightTraceRemainder σ β x| ≤ B := by
      unfold primeRightTraceRemainder
      apply (abs_add_le _ _).trans
      apply (add_le_add ((abs_sub _ _).trans (add_le_add hψ
        (by simpa only [abs_of_nonneg hx0] using hxY))) htrace').trans_eq
      rfl
    exact hbound.trans ((le_add_of_nonneg_left hC).trans
      (le_mul_of_one_le_right (add_nonneg hC hB) hxκ))

end GaloisForLFunctions.ZeroConfigurationGeometry
