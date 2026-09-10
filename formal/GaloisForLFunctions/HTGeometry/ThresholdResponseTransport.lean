import GaloisForLFunctions.HTGeometry.ThresholdResponseCuts
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Threshold-layer transport control for finite responses

The threshold-layer mechanism of Araújo, arXiv:2609.05560, Theorem 10 is instantiated for
finite affine-plus-jump response laws and explicit atomic pairings. The radius is constructed
as `exp r`, so the estimates require no supplied positivity hypothesis. A single-atom
family also proves that pairing costs can tend to zero while response distortion remains one.
-/
open scoped BigOperators Topology
open Filter
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Every oriented step has unit oscillation. -/
theorem orientedResponseStep_oscillation (closed : Bool) (threshold u v : ℝ) :
    |orientedResponseStep closed threshold v - orientedResponseStep closed threshold u| ≤ 1 := by
  unfold orientedResponseStep
  split_ifs <;> norm_num

/-- A step discrepancy requires either transport across the chosen radius or source mass near
its threshold. The radius is positive for every real parameter. -/
theorem orientedResponseStep_threshold_bound (closed : Bool) (threshold u v r : ℝ) :
    |orientedResponseStep closed threshold v - orientedResponseStep closed threshold u| ≤
      |v - u| / (Real.exp r) + (if |u - threshold| ≤ Real.exp r then 1 else 0) := by
  have hd : 0 < Real.exp r := by positivity
  have hcost : 0 ≤ |v - u| / (Real.exp r) := by positivity
  by_cases hsame : orientedResponseStep closed threshold v = orientedResponseStep closed threshold u
  · rw [hsame, sub_self, abs_zero]
    split_ifs <;> positivity
  have hc : |u - threshold| ≤ |v - u| := by
    cases closed <;> simp only [orientedResponseStep, Bool.false_eq_true, if_false, if_true] at hsame
    all_goals split_ifs at hsame with hv hu
    all_goals try simp at hsame
    all_goals
      rw [abs_le]
      constructor <;> linarith [le_abs_self (v - u), neg_le_abs (v - u)]
  have ho := orientedResponseStep_oscillation closed threshold u v
  by_cases hl : |u - threshold| ≤ Real.exp r
  · rw [if_pos hl]
    linarith
  · rw [if_neg hl, add_zero]
    have hlarge : Real.exp r ≤ |v - u| := le_trans (le_of_not_ge hl) hc
    exact ho.trans ((le_div_iff₀ hd).mpr (by simpa using hlarge))

/-- Absolute source mass lying in a closed layer around one recipient-offset threshold. -/
def finiteThresholdLayerMass {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (threshold x r : ℝ) : ℝ :=
  ∑ i, |w i| * (if |z i - x - threshold| ≤ Real.exp r then 1 else 0)

/-- A single response threshold obeys the explicit-pairing transport/layer bound. -/
theorem finiteResponseForce_step_transport_bound {ι : Type*} [Fintype ι]
    (w z t : ι → ℝ) (closed : Bool) (threshold x r : ℝ) :
    |finiteResponseForce (orientedResponseStep closed threshold) w t x -
      finiteResponseForce (orientedResponseStep closed threshold) w z x| ≤
        finiteResponsePairingCost w z t / (Real.exp r) + finiteThresholdLayerMass w z threshold x r := by
  unfold finiteResponseForce
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |w i * orientedResponseStep closed threshold (t i - x) -
      w i * orientedResponseStep closed threshold (z i - x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * (|t i - z i| / (Real.exp r) +
      (if |z i - x - threshold| ≤ Real.exp r then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg (w i))
      simpa only [show t i - x - (z i - x) = t i - z i by ring] using
        orientedResponseStep_threshold_bound closed threshold (z i - x) (t i - x) r
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div,
        finiteResponsePairingCost, finiteThresholdLayerMass]

/-- Jump-weighted threshold-layer mass over a finite recipient panel. -/
def finiteJumpLayerPanel {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    (w z : ι → ℝ) (jump threshold : κ → ℝ) (r : ℝ)
    (probe : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => ∑ k, |jump k| * finiteThresholdLayerMass w z (threshold k) (probe j) r

/-- All jump errors are controlled by transport and the largest weighted threshold layer. -/
theorem finiteJumpDiscrepancy_transport_bound {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    (w z t : ι → ℝ) (jump threshold : κ → ℝ) (closed : κ → Bool) (r : ℝ)
    (probe : Fin (n + 1) → ℝ) :
    finiteJumpDiscrepancy w z t jump threshold closed probe ≤
      (∑ k, |jump k|) * (finiteResponsePairingCost w z t / (Real.exp r)) +
        ‖finiteJumpLayerPanel w z jump threshold r probe‖ := by
  unfold finiteJumpDiscrepancy
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro j
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ k, |jump k *
      (finiteResponseForce (orientedResponseStep (closed k) (threshold k)) w t (probe j) -
        finiteResponseForce (orientedResponseStep (closed k) (threshold k)) w z (probe j))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |jump k| * (finiteResponsePairingCost w z t / (Real.exp r) +
      finiteThresholdLayerMass w z (threshold k) (probe j) r) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (finiteResponseForce_step_transport_bound w z t (closed k) (threshold k) (probe j) r)
        (abs_nonneg (jump k))
    _ = (∑ k, |jump k|) * (finiteResponsePairingCost w z t / (Real.exp r)) +
      finiteJumpLayerPanel w z jump threshold r probe j := by
        simp [finiteJumpLayerPanel, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ _ := add_le_add le_rfl
      ((le_abs_self _).trans (norm_le_pi_norm (finiteJumpLayerPanel w z jump threshold r probe) j))

/-- The affine-plus-jump specialization of the threshold-aware transport estimate. -/
theorem finiteResponseDistortion_threshold_transport_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] {n : ℕ}
    (w z t : ι → ℝ) (a b : ℝ) (jump threshold : κ → ℝ) (closed : κ → Bool) (r : ℝ)
    (probe : Fin (n + 1) → ℝ) :
    finiteResponseDistortion (affineJumpResponse a b jump threshold closed) w z w t probe ≤
      |a| * finiteResponsePairingCost w z t +
        (∑ k, |jump k|) * (finiteResponsePairingCost w z t / (Real.exp r)) +
          ‖finiteJumpLayerPanel w z jump threshold r probe‖ := by
  have hs := (abs_le.mp (finiteResponseDistortion_jump_sandwich_transport
    w z t a b jump threshold closed probe)).2
  have hj := finiteJumpDiscrepancy_transport_bound w z t jump threshold closed r probe
  linarith

/-- A vanishing displacement moves one atom from the closed threshold to its lower side. -/
def thresholdCrossingNode (m : ℕ) : Fin 1 → ℝ := fun _ => -(1 / (m + 1 : ℝ))

theorem thresholdCrossing_pairing_cost (m : ℕ) :
    finiteResponsePairingCost (fun _ : Fin 1 => 1) (fun _ => 0) (thresholdCrossingNode m) =
      1 / (m + 1 : ℝ) := by
  have hn : (0 : ℝ) ≤ m + 1 := by positivity
  simp [finiteResponsePairingCost, thresholdCrossingNode, hn]

/-- Transport-small single-atom summaries retain unit threshold response error. -/
theorem thresholdCrossing_distortion_one (m : ℕ) :
    finiteResponseDistortion (orientedResponseStep true 0)
      (fun _ : Fin 1 => 1) (fun _ => 0)
      (fun _ : Fin 1 => 1) (thresholdCrossingNode m) (fun _ : Fin 1 => 0) = 1 := by
  have hn : (0 : ℝ) < m + 1 := by positivity
  simp [finiteResponseDistortion, finiteResponseForce, thresholdCrossingNode, orientedResponseStep, not_le.mpr hn]

/-- The counterexample has transport cost converging to zero, with no asymptotic premise. -/
theorem thresholdCrossing_transport_tendsto_zero :
    Tendsto (fun m => finiteResponsePairingCost (fun _ : Fin 1 => 1)
      (fun _ => 0) (thresholdCrossingNode m)) atTop (𝓝 0) := by
  simp_rw [thresholdCrossing_pairing_cost]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end
end GaloisForLFunctions.HTGeometry
