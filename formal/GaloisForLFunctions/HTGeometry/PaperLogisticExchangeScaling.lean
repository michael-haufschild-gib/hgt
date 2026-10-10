import GaloisForLFunctions.HTGeometry.PaperLogisticExchangeWork
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Diffusive scaling of logistic information work

The reflected phase contrast has derivative one half at neutrality, so symmetric
relative entropy is asymptotic to the square of the grade. At grades `1/(n+1)` and
depths `(n+1)^2`, each grade tends to zero but the total information tends to one.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

theorem paperLogisticContrast_eq (a : ℝ) :
    (logisticPhase a : ℝ) - (logisticPhase (-a) : ℝ) =
      (Real.exp a - 1) / (Real.exp a + 1) := by
  simp only [coe_logisticPhase, Real.exp_neg]
  have he := (Real.exp_pos a).ne'
  have hd : Real.exp a + 1 ≠ 0 := by positivity
  have hd' : 1 + Real.exp a ≠ 0 := by positivity
  field_simp
  ring

theorem paperLogisticContrast_div_tendsto :
    Tendsto (fun a : ℝ =>
      ((logisticPhase a : ℝ) - (logisticPhase (-a) : ℝ)) / a)
      (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have hd : HasDerivAt (fun a : ℝ => (Real.exp a - 1) / (Real.exp a + 1))
      (1 / 2) 0 := by
    convert! ((Real.hasDerivAt_exp 0).sub_const 1).div
      ((Real.hasDerivAt_exp 0).add_const 1) (by norm_num) using 1
    norm_num
  simp_rw [paperLogisticContrast_eq]
  simpa [div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero

/-- Symmetric information has unit quadratic coefficient at the neutral grade. -/
theorem paperLogisticExchangeInformation_quadratic_limit :
    Tendsto (fun a : ℝ => paperLogisticExchangeInformation a / a ^ 2)
      (𝓝[≠] 0) (𝓝 1) := by
  have h : Tendsto (fun a : ℝ => 2 *
      (((logisticPhase a : ℝ) - (logisticPhase (-a) : ℝ)) / a))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul paperLogisticContrast_div_tendsto
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : a ≠ 0 := by simpa using ha
  rw [paperLogisticExchangeInformation_eq]
  field_simp

/-- A nonzero grade for every finite depth parameter. -/
def paperLogisticDiffusiveGrade (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem paperLogisticDiffusiveGrade_pos (n : ℕ) : 0 < paperLogisticDiffusiveGrade n := by
  unfold paperLogisticDiffusiveGrade
  positivity

theorem paperLogisticDiffusiveGrade_tendsto :
    Tendsto paperLogisticDiffusiveGrade atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem diffusiveGrade_tendsto_punctured :
    Tendsto paperLogisticDiffusiveGrade atTop (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨paperLogisticDiffusiveGrade_tendsto,
    Eventually.of_forall (fun n => (paperLogisticDiffusiveGrade_pos n).ne')⟩

theorem paperLogisticDiffusiveContrast_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      ((logisticPhase (paperLogisticDiffusiveGrade n) : ℝ) -
        (logisticPhase (-paperLogisticDiffusiveGrade n) : ℝ))) atTop (𝓝 (1 / 2)) := by
  simpa [Function.comp_def, paperLogisticDiffusiveGrade, div_eq_mul_inv, mul_comm] using
    paperLogisticContrast_div_tendsto.comp diffusiveGrade_tendsto_punctured

/-- Increasing depth preserves a positive total information cost as the grade vanishes. -/
theorem paperLogisticDiffusiveInformation_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 *
      paperLogisticExchangeInformation (paperLogisticDiffusiveGrade n)) atTop (𝓝 1) := by
  simpa [Function.comp_def, paperLogisticDiffusiveGrade, div_pow, div_eq_mul_inv, mul_comm] using
    paperLogisticExchangeInformation_quadratic_limit.comp diffusiveGrade_tendsto_punctured

/-- The same limit holds for the literal native repeated-experiment divergence. -/
theorem paperLogisticDiffusiveSlotWork_tendsto :
    Tendsto (fun n : ℕ =>
      (slotWork
        (paperLogisticLaw (paperLogisticDiffusiveGrade n) |>.atomicProbability id : Measure Bool)
        (paperLogisticLaw (-paperLogisticDiffusiveGrade n) |>.atomicProbability id : Measure Bool)
        ((n + 1) ^ 2)).toReal) atTop (𝓝 1) := by
  simpa only [paperLogisticLaw_slotWork_toReal, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    paperLogisticDiffusiveInformation_tendsto

/-- One finite bound covers all these increasing depths, despite nonzero grades at every stage. -/
theorem paperLogisticDiffusiveSlotWork_bounded :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n : ℕ,
      slotWork
        (paperLogisticLaw (paperLogisticDiffusiveGrade n) |>.atomicProbability id : Measure Bool)
        (paperLogisticLaw (-paperLogisticDiffusiveGrade n) |>.atomicProbability id : Measure Bool)
        ((n + 1) ^ 2) ≤ C := by
  obtain ⟨C, hC⟩ := paperLogisticDiffusiveInformation_tendsto.bddAbove_range
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n => ?_⟩
  rw [paperLogisticLaw_slotWork]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hC (Set.mem_range_self n)

end
end GaloisForLFunctions.HTGeometry
