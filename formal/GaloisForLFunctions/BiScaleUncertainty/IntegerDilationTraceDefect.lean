import GaloisForLFunctions.BiScaleUncertainty.IntegerBlockVariance
import GaloisForLFunctions.BiScaleUncertainty.DivisorPhysicalProjection
import GaloisForLFunctions.BiScaleUncertainty.FullDivisorEnergyEscape

/-!
# Exact infinite dilation defect and additive covariance

The physical trace deficit splits into noncellular energy and convergent
block variance. Explicit packets attain the sharp coefficient. Integer block
aggregation intertwines a shift by one block with the successor shift.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def sequenceShiftPower : ℕ → TraceData →L[ℝ] TraceData
  | 0 => ContinuousLinearMap.id ℝ TraceData
  | n+1 => (sequenceRightShift ℝ).toContinuousLinearMap ∘L sequenceShiftPower n

theorem sequenceShiftPower_zero (w : TraceData) : sequenceShiftPower 0 w = w := rfl

theorem sequenceShiftPower_succ (n : ℕ) (w : TraceData) :
    sequenceShiftPower (n+1) w = sequenceRightShift ℝ (sequenceShiftPower n w) := rfl

theorem sequenceShiftPower_eq_pow (n : ℕ) :
    sequenceShiftPower n = (sequenceRightShift ℝ).toContinuousLinearMap^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (sequenceRightShift ℝ).toContinuousLinearMap ∘L sequenceShiftPower n = _
      rw [ih, pow_succ']
      rfl

theorem sequenceShiftPower_coordinate (n : ℕ) (w : TraceData) (k : ℕ) :
    sequenceShiftPower n w k = if k < n then 0 else w (k-n) := by
  induction n generalizing k with
  | zero => simp [sequenceShiftPower_zero]
  | succ n ih =>
      cases k with
      | zero => simp [sequenceShiftPower_succ, sequenceRightShift_zero]
      | succ k =>
          rw [sequenceShiftPower_succ, sequenceRightShift_succ, ih]
          simp

theorem cellPrefixL_sequenceShiftPower (m n : ℕ) (w : TraceData) :
    cellPrefixL n (sequenceShiftPower m w) = cellPrefixL (n-m) w := by
  induction n with
  | zero => simp [cellPrefixL_zero]
  | succ n ih =>
      rw [cellPrefixL_succ, ih, sequenceShiftPower_coordinate]
      by_cases h : n < m
      · have hn : n-m = 0 := by omega
        have hs : n+1-m = 0 := by omega
        simp [h, hn, hs, cellPrefixL_zero]
      · have hs : n+1-m = (n-m)+1 := by omega
        rw [if_neg h, hs, cellPrefixL_succ]

theorem integerBlockSum_shift (m : ℕ) (w : TraceData) :
    integerBlockSum m (sequenceShiftPower m w) = sequenceRightShift ℝ (integerBlockSum m w) := by
  apply lp.ext
  funext j
  rw [integerBlockSum_prefix_difference, cellPrefixL_sequenceShiftPower,
    cellPrefixL_sequenceShiftPower]
  cases j with
  | zero => simp [sequenceRightShift_zero, cellPrefixL_zero]
  | succ j =>
      rw [sequenceRightShift_succ, integerBlockSum_prefix_difference]
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]

theorem physicalDilation_trace_defect (m : ℕ) (q : Velocity) :
    (m : ℝ)*‖q‖^2-‖unitCellAnalysis (physicalDilation m q)‖^2 =
      (m : ℝ)*‖q-cellularProjection q‖^2+∑' j, integerBlockVariance m (unitCellAnalysis q) j := by
  rw [unitCellAnalysis_physicalDilation, integerBlockVariance_tsum]
  have h := congrArg (fun x : ℝ => (m : ℝ)*x) (cellularProjection_energy q)
  nlinarith only [h]

theorem physicalDilation_trace_energy_le (m : ℕ) (q : Velocity) :
    ‖unitCellAnalysis (physicalDilation m q)‖^2 ≤ (m : ℝ)*‖q‖^2 := by
  have h := physicalDilation_trace_defect m q
  have hv : 0 ≤ ∑' j, integerBlockVariance m (unitCellAnalysis q) j :=
    tsum_nonneg (integerBlockVariance_nonneg m (unitCellAnalysis q))
  have hc := mul_nonneg (Nat.cast_nonneg m) (sq_nonneg ‖q-cellularProjection q‖)
  linarith only [h, hv, hc]

theorem physicalDilation_trace_energy_eq_iff (n : ℕ) (q : Velocity) :
    ‖unitCellAnalysis (physicalDilation ((n+1 : ℕ) : ℝ) q)‖^2 =
      ((n+1 : ℕ) : ℝ)*‖q‖^2 ↔
        q = cellularProjection q ∧ IntegerBlockConstant (n+1) (unitCellAnalysis q) := by
  constructor
  · intro h
    have he := physicalDilation_trace_defect (n+1) q
    have hv : 0 ≤ ∑' j, integerBlockVariance (n+1) (unitCellAnalysis q) j :=
      tsum_nonneg (integerBlockVariance_nonneg (n+1) (unitCellAnalysis q))
    have hp : 0 < ((n+1 : ℕ) : ℝ) := by positivity
    have hc : ((n+1 : ℕ) : ℝ)*‖q-cellularProjection q‖^2 = 0 := by
      apply le_antisymm _ (mul_nonneg hp.le (sq_nonneg _))
      linarith only [he, h, hv]
    have hz : ‖q-cellularProjection q‖^2 = 0 := (mul_eq_zero.mp hc).resolve_left hp.ne'
    have hq : q = cellularProjection q := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    refine ⟨hq, (integerBlockSum_energy_eq_iff _ _).mp ?_⟩
    have hb : ‖unitCellAnalysis q‖^2 = ‖q‖^2 := by
      have ht := cellularProjection_energy q
      linarith only [ht, hz]
    rw [← unitCellAnalysis_physicalDilation, h, hb]
  · rintro ⟨hq, hc⟩
    have hz : q-cellularProjection q = 0 := sub_eq_zero.mpr hq
    have hb : ‖unitCellAnalysis q‖^2 = ‖q‖^2 := by
      simpa only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
        cellularProjection_energy q
    rw [unitCellAnalysis_physicalDilation, (integerBlockSum_energy_eq_iff _ _).mpr hc, hb]

def blockPhysicalPacket (m : ℕ) : Velocity :=
  unitCellSynthesis (integerBlockReplicate m (lp.single 2 0 1))

theorem blockPhysicalPacket_energy (m : ℕ) : ‖blockPhysicalPacket m‖^2 = (m : ℝ) := by
  rw [blockPhysicalPacket, unitCellSynthesis.norm_map, integerBlockReplicate_energy]
  simp

theorem blockPhysicalPacket_trace_energy (m : ℕ) :
    ‖unitCellAnalysis (physicalDilation m (blockPhysicalPacket m))‖^2 = (m : ℝ)^2 := by
  rw [unitCellAnalysis_physicalDilation, blockPhysicalPacket, unitCellAnalysis_synthesis,
    integerBlockSum_replicate, norm_smul]
  simp

theorem blockPhysicalPacket_ne_zero (n : ℕ) : blockPhysicalPacket (n+1) ≠ 0 := by
  intro h
  have he := blockPhysicalPacket_energy (n+1)
  rw [h, norm_zero, zero_pow (by decide)] at he
  have hp : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  linarith only [he, hp]

theorem unitCell_one_in_full_completion (d : ℕ) :
    unitCell 1 ∈ Set.range (divisorEnergyExtension d Set.univ) :=
  ⟨fullDivisorEscape d, fullDivisorEscape_extension d⟩

/-- Even the full-family completed divisor domain is not invariant under dilation. -/
theorem dilation_two_outside_divisor_completion (d : ℕ) (D : Set ℕ) :
    physicalDilation 2 (unitCell 1) ∉ Set.range (divisorEnergyExtension d D) := by
  rintro ⟨v, hv⟩
  have h0 := divisorPhysicalProjection_first_trace d D (divisorEnergyExtension d D v)
  rw [divisorPhysicalProjection_extension, hv] at h0
  have h1 : primitive (physicalDilation 2 (unitCell 1)) 1 = 1 := by
    rw [primitive_physicalDilation, mul_one]
    have hi := inner_prefixCell 2 (unitCell 1)
    rw [inner_prefixCell_unitCell] at hi
    norm_num at hi
    exact hi.symm
  linarith only [h0, h1]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
