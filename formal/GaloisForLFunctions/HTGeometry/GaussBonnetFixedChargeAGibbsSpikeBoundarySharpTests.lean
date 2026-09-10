import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeBoundaryIntegrals

/-! # A continuous witness for the sharp dimensional variation bound -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- A bounded continuous function separates the endpoint deficit from both retained atoms. -/
def egbFixedChargeAGibbsSpikeBoundaryWitness (y : HausdorffSourceSpace) : ℝ :=
  min 1 (-1 + 72 * (y : ℝ))

/-- The exact integral error is bounded using only the three relevant function values. -/
theorem egbFixedChargeAGibbsSpike_integral_error_bound (n : ℕ) (f : HausdorffSourceSpace → ℝ) :
    |(∫ y, f y ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)) -
      (∫ y, f y ∂egbFixedChargeAGibbsSpikeBoundarySource)| ≤
      9 / (4 * (2 : ℝ) ^ (n + 3)) *
        max |f egbFixedChargeAGibbsCollisionZeroNode|
          (max |f egbFixedChargeAGibbsCollisionSlowNode| |f egbFixedChargeAGibbsCollisionFastNode|) := by
  let M := max |f egbFixedChargeAGibbsCollisionZeroNode|
    (max |f egbFixedChargeAGibbsCollisionSlowNode| |f egbFixedChargeAGibbsCollisionFastNode|)
  have h0 : |f egbFixedChargeAGibbsCollisionZeroNode| ≤ M := le_max_left _ _
  have hr : |f egbFixedChargeAGibbsCollisionSlowNode| ≤ M :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hs : |f egbFixedChargeAGibbsCollisionFastNode| ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hnum : |-5 * f egbFixedChargeAGibbsCollisionZeroNode +
      2 * f egbFixedChargeAGibbsCollisionSlowNode + 2 * f egbFixedChargeAGibbsCollisionFastNode| ≤ 9 * M := by
    have h0' := abs_le.mp h0
    have hr' := abs_le.mp hr
    have hs' := abs_le.mp hs
    rw [abs_le]
    constructor <;> linarith
  have hd : 0 < 4 * (2 : ℝ) ^ (n + 3) := by positivity
  rw [egbFixedChargeAGibbsSpike_integral_error, abs_div, abs_of_pos hd]
  calc
    _ ≤ (9 * M) / (4 * (2 : ℝ) ^ (n + 3)) := div_le_div_of_nonneg_right hnum hd.le
    _ = _ := by ring

/-- The saturating witness is continuous on the whole Hausdorff interval. -/
theorem egbFixedChargeAGibbsSpike_boundary_witness_continuous :
    Continuous egbFixedChargeAGibbsSpikeBoundaryWitness := by
  unfold egbFixedChargeAGibbsSpikeBoundaryWitness
  fun_prop

/-- The witness has absolute value at most one everywhere. -/
theorem egbFixedChargeAGibbsSpike_boundary_witness_bounded (y : HausdorffSourceSpace) :
    |egbFixedChargeAGibbsSpikeBoundaryWitness y| ≤ 1 := by
  rw [abs_le]
  constructor
  · exact le_min (by norm_num) (by have hy := y.property.1; linarith)
  · exact min_le_left _ _

/-- One continuous unit-bounded test attains the entire total variation mass. -/
theorem egbFixedChargeAGibbsSpike_boundary_witness_error (n : ℕ) :
    (∫ y, egbFixedChargeAGibbsSpikeBoundaryWitness y
      ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)) -
      (∫ y, egbFixedChargeAGibbsSpikeBoundaryWitness y ∂egbFixedChargeAGibbsSpikeBoundarySource) =
      9 / (4 * (2 : ℝ) ^ (n + 3)) := by
  rw [egbFixedChargeAGibbsSpike_integral_error]
  norm_num [egbFixedChargeAGibbsSpikeBoundaryWitness, egbFixedChargeAGibbsCollisionZeroNode,
    egbFixedChargeAGibbsCollisionSlowNode, egbFixedChargeAGibbsCollisionFastNode]

/-- The exact maximum testing error over all continuous unit-bounded real functions. -/
theorem egbFixedChargeAGibbsSpike_boundary_continuous_test_maximum (n : ℕ) :
    IsGreatest {z : ℝ | ∃ f : HausdorffSourceSpace → ℝ,
      Continuous f ∧ (∀ y, |f y| ≤ 1) ∧ z =
        |(∫ y, f y ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)) -
          (∫ y, f y ∂egbFixedChargeAGibbsSpikeBoundarySource)|}
      (9 / (4 * (2 : ℝ) ^ (n + 3))) := by
  constructor
  · refine ⟨egbFixedChargeAGibbsSpikeBoundaryWitness,
      egbFixedChargeAGibbsSpike_boundary_witness_continuous,
      egbFixedChargeAGibbsSpike_boundary_witness_bounded, ?_⟩
    rw [egbFixedChargeAGibbsSpike_boundary_witness_error, abs_of_nonneg (by positivity)]
  · rintro z ⟨f, _, hf, rfl⟩
    have hm : max |f egbFixedChargeAGibbsCollisionZeroNode|
        (max |f egbFixedChargeAGibbsCollisionSlowNode| |f egbFixedChargeAGibbsCollisionFastNode|) ≤ 1 :=
      max_le (hf _) (max_le (hf _) (hf _))
    have h := egbFixedChargeAGibbsSpike_integral_error_bound n f
    exact h.trans (by nlinarith [show 0 ≤ 9 / (4 * (2 : ℝ) ^ (n + 3)) by positivity])

end
end GaloisForLFunctions.HTGeometry
