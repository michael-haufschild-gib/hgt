import GaloisForLFunctions.BiScaleUncertainty.DivisorCellEndpoints
import GaloisForLFunctions.BiScaleUncertainty.DivisorEnergyCompletion

/-!
# Explicit component means and admitted centered currents

The orthogonal residual is the finite-component mean at every cell, with
zero correction on infinite active tails. These finite formulas construct
actual square-summable currents and admitted completed trace data.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def divisorCellResidual (d : ℕ) (D : Set ℕ) (w : TraceData) : TraceData :=
  w - (divisorCellSpace d D).starProjection w

theorem divisorCellResidual_orthogonal (d : ℕ) (D : Set ℕ) (w : TraceData) :
    divisorCellResidual d D w ∈ (divisorCellSpace d D)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal w

theorem divisorCellResidual_component (d : ℕ) (D : Set ℕ) (w : TraceData)
    (a b : ℕ) (h : DivisorFiniteComponent d D a b) (k : ℕ) (hk : a ≤ k ∧ k < b) :
    divisorCellResidual d D w k =
      (∑ i ∈ Finset.Ico a b, w i) / ((b-a : ℕ) : ℝ) := by
  let r := divisorCellResidual d D w
  have hr := divisorCellResidual_orthogonal d D w
  have hc (i : ℕ) (hi : i ∈ Finset.Ico a b) : r i = r a := by
    have hi' := Finset.mem_Ico.mp hi
    have he := divisorCell_orthogonal_component d D ⟨r, hr⟩ a b h (i-a) (by omega)
    simpa only [show a+(i-a)=i by omega] using he
  have hp : ∑ i ∈ Finset.Ico a b, ((divisorCellSpace d D).starProjection w) i = 0 :=
    divisorCell_component_sum_zero d D
      ⟨_, Submodule.starProjection_apply_mem _ _⟩ a b h
  have hs : (∑ i ∈ Finset.Ico a b, r i) = ∑ i ∈ Finset.Ico a b, w i := by
    simp only [r, divisorCellResidual, lp.coeFn_sub, Pi.sub_apply,
      Finset.sum_sub_distrib, hp, sub_zero]
  have ht : (∑ i ∈ Finset.Ico a b, r i) = ((b-a : ℕ) : ℝ) * r a := by
    calc
      _ = ∑ _i ∈ Finset.Ico a b, r a := Finset.sum_congr rfl hc
      _ = _ := by simp
  have hab := h.1
  have hn : ((b-a : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < b-a := by omega
    exact_mod_cast hpos.ne'
  change r k = _
  rw [hc k (Finset.mem_Ico.mpr hk), ← hs, ht]
  field_simp

theorem divisorCellResidual_noEnd (d : ℕ) (D : Set ℕ) (w : TraceData) (k : ℕ)
    (h : ¬ divisorCellHasEnd d D k) : divisorCellResidual d D w k = 0 := by
  have ht (n : ℕ) : divisorGridActive d D (k+n) := by
    by_contra hn
    exact h ⟨n, hn⟩
  simpa only [Nat.add_zero] using divisorCell_orthogonal_tail_zero d D
    ⟨_, divisorCellResidual_orthogonal d D w⟩ k ht 0

def divisorEndpointMean (d : ℕ) (D : Set ℕ) (w : TraceData) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.Ico (divisorCellStart d D j) (j+1), w i) /
    (divisorComponentLength d D j : ℝ)

def divisorComponentMean (d : ℕ) (D : Set ℕ) (w : TraceData) (k : ℕ) : ℝ :=
  if divisorCellHasEnd d D k then divisorEndpointMean d D w (divisorCellEnd d D k) else 0

/-- Finite arithmetic means equal the actual Hilbert residual, including infinite tails. -/
theorem divisorComponentMean_eq_residual (d : ℕ) (D : Set ℕ) (w : TraceData) (k : ℕ) :
    divisorComponentMean d D w k = divisorCellResidual d D w k := by
  by_cases h : divisorCellHasEnd d D k
  · rw [divisorComponentMean, if_pos h]
    have hj := not_active_divisorCellEnd d D k h
    have hk : divisorCellStart d D (divisorCellEnd d D k) ≤ k ∧
        k < divisorCellEnd d D k+1 := by
      rw [divisorCellStart_end d D k h]
      exact ⟨divisorCellStart_le d D k, by have := divisorCellEnd_ge d D k; omega⟩
    exact (divisorCellResidual_component d D w _ _
      (divisorCellStart_component d D _ hj) k hk).symm
  · rw [divisorComponentMean, if_neg h, divisorCellResidual_noEnd d D w k h]

theorem divisorComponentMean_on_component (d : ℕ) (D : Set ℕ) (w : TraceData)
    (j : ℕ) (hj : ¬ divisorGridActive d D j) (k : ℕ)
    (hk : divisorCellStart d D j ≤ k ∧ k < j+1) :
    divisorComponentMean d D w k = divisorEndpointMean d D w j := by
  rw [divisorComponentMean_eq_residual]
  exact divisorCellResidual_component d D w _ _ (divisorCellStart_component d D j hj) k hk

/-- The concrete finite-mean formula is square-summable for every ambient current. -/
def divisorMeanCurrent (d : ℕ) (D : Set ℕ) (w : TraceData) : TraceData :=
  ⟨divisorComponentMean d D w, by
    have he : divisorComponentMean d D w = (divisorCellResidual d D w : ℕ → ℝ) :=
      funext (divisorComponentMean_eq_residual d D w)
    rw [he]
    exact lp.memℓp _⟩

theorem divisorMeanCurrent_apply (d : ℕ) (D : Set ℕ) (w : TraceData) (k : ℕ) :
    divisorMeanCurrent d D w k = divisorComponentMean d D w k := rfl

theorem divisorMeanCurrent_eq_residual (d : ℕ) (D : Set ℕ) (w : TraceData) :
    divisorMeanCurrent d D w = divisorCellResidual d D w := by
  apply lp.ext
  exact funext (divisorComponentMean_eq_residual d D w)

theorem divisor_centered_eq_projection (d : ℕ) (D : Set ℕ) (w : TraceData) :
    w - divisorMeanCurrent d D w = (divisorCellSpace d D).starProjection w := by
  rw [divisorMeanCurrent_eq_residual, divisorCellResidual]
  abel

def divisorCenteredData (d : ℕ) (D : Set ℕ) (w : TraceData) : DivisorEnergyData d D :=
  ⟨w-divisorMeanCurrent d D w, by
    rw [divisor_centered_eq_projection]
    exact Submodule.starProjection_apply_mem _ _⟩

theorem divisorCenteredData_apply (d : ℕ) (D : Set ℕ) (w : TraceData) (k : ℕ) :
    (divisorCenteredData d D w).1 k = w k - divisorComponentMean d D w k := by
  simp only [divisorCenteredData, lp.coeFn_sub, Pi.sub_apply, divisorMeanCurrent_apply]

theorem divisorCenteredData_eq_projection (d : ℕ) (D : Set ℕ) (w : TraceData) :
    (divisorCenteredData d D w).1 = (divisorCellSpace d D).starProjection w :=
  divisor_centered_eq_projection d D w

theorem divisorCenteredData_norm_le (d : ℕ) (D : Set ℕ) (w : TraceData) :
    ‖divisorCenteredData d D w‖ ≤ ‖w‖ := by
  change ‖(divisorCenteredData d D w).1‖ ≤ ‖w‖
  rw [divisorCenteredData_eq_projection]
  exact (divisorCellSpace d D).norm_starProjection_apply_le w

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
