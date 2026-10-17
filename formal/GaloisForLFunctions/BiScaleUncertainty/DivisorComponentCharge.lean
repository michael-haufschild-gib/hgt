import GaloisForLFunctions.BiScaleUncertainty.DivisorComponentAverages
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The convergent arithmetic component charge

Every finite component contributes its squared total current divided by its
length. Grouping the actual square-summable residual by canonical endpoints
proves summability and the exact error, without a convergence premise.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def divisorComponentCharge (d : ℕ) (D : Set ℕ) (w : TraceData) (j : ℕ) : ℝ :=
  if divisorGridActive d D j then 0 else
    (∑ i ∈ Finset.Ico (divisorCellStart d D j) (j+1), w i)^2 /
      (divisorComponentLength d D j : ℝ)

theorem divisorComponentCharge_nonneg (d : ℕ) (D : Set ℕ) (w : TraceData) (j : ℕ) :
    0 ≤ divisorComponentCharge d D w j := by
  unfold divisorComponentCharge
  split_ifs
  · exact le_rfl
  · positivity

theorem divisorComponentCharge_fibre (d : ℕ) (D : Set ℕ) (w : TraceData) (j : ℕ) :
    (∑' k : divisorCellEnd d D ⁻¹' {j}, (divisorMeanCurrent d D w k.1)^2) =
      divisorComponentCharge d D w j := by
  by_cases hj : divisorGridActive d D j
  · rw [divisorComponentCharge, if_pos hj]
    have hz (k : divisorCellEnd d D ⁻¹' {j}) : (divisorMeanCurrent d D w k.1)^2 = 0 := by
      have he : divisorCellEnd d D k.1 = j := k.2
      have hn := divisorCellEnd_active_noEnd d D k.1 j hj he
      simp [divisorMeanCurrent_apply, divisorComponentMean, hn]
    simp only [hz, tsum_zero]
  · rw [divisorCellEnd_fibre d D j hj, divisorComponentCharge, if_neg hj]
    have hn : (divisorComponentLength d D j : ℝ) ≠ 0 := by
      exact_mod_cast (divisorComponentLength_pos d D j).ne'
    calc
      _ = ∑ k ∈ Finset.Ico (divisorCellStart d D j) (j+1),
          (divisorMeanCurrent d D w k)^2 :=
        Finset.tsum_subtype' _ (fun k => (divisorMeanCurrent d D w k)^2)
      _ = ∑ _k ∈ Finset.Ico (divisorCellStart d D j) (j+1), (divisorEndpointMean d D w j)^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [divisorMeanCurrent_apply, divisorComponentMean_on_component d D w j hj k
          (Finset.mem_Ico.mp hk)]
      _ = (divisorComponentLength d D j : ℝ) * (divisorEndpointMean d D w j)^2 := by
        simp [divisorComponentLength]
      _ = _ := by
        unfold divisorEndpointMean
        field_simp

/-- The charge series is proved convergent from the actual ℓ² residual. -/
theorem hasSum_divisorComponentCharge (d : ℕ) (D : Set ℕ) (w : TraceData) :
    HasSum (divisorComponentCharge d D w) (‖divisorMeanCurrent d D w‖^2) := by
  have hs : Summable (fun k => (divisorMeanCurrent d D w k)^2) := by
    simpa only [Real.inner_apply, pow_two] using
      lp.summable_inner (𝕜 := ℝ) (divisorMeanCurrent d D w) (divisorMeanCurrent d D w)
  have ht := hs.hasSum.tsum_fiberwise (divisorCellEnd d D)
  rw [← norm_sq_traceData] at ht
  exact ht.congr_fun (fun j => (divisorComponentCharge_fibre d D w j).symm)

theorem summable_divisorComponentCharge (d : ℕ) (D : Set ℕ) (w : TraceData) :
    Summable (divisorComponentCharge d D w) := (hasSum_divisorComponentCharge d D w).summable

theorem divisorComponentCharge_tsum (d : ℕ) (D : Set ℕ) (w : TraceData) :
    ∑' j, divisorComponentCharge d D w j = ‖divisorMeanCurrent d D w‖^2 :=
  (hasSum_divisorComponentCharge d D w).tsum_eq

theorem divisorCenteredData_energy (d : ℕ) (D : Set ℕ) (w : TraceData) :
    ‖divisorCenteredData d D w‖^2 + ∑' j, divisorComponentCharge d D w j = ‖w‖^2 := by
  rw [divisorComponentCharge_tsum, divisorMeanCurrent_eq_residual]
  change ‖(divisorCenteredData d D w).1‖^2 + ‖divisorCellResidual d D w‖^2 = _
  rw [divisorCenteredData_eq_projection, divisorCellResidual]
  simpa only [Submodule.starProjection_orthogonal_val] using
    (Submodule.norm_sq_eq_add_norm_sq_starProjection w (divisorCellSpace d D)).symm

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
