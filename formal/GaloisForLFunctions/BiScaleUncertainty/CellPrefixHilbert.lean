import GaloisForLFunctions.BiScaleUncertainty.FinitePathSinePackets
import GaloisForLFunctions.BiScaleUncertainty.DivisorGridTraceData

/-!
# Cell currents, cumulative traces and physical synthesis

Finite prefix functionals recover the integer traces of actual unit-cell
synthesis. Their discrete gradient is exact, and square-summable currents
cannot carry a nonzero constant infinite tail.
-/

noncomputable section
open Filter
open scoped RealInnerProductSpace Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def cellPrefixL (n : ℕ) : TraceData →L[ℝ] ℝ :=
  innerSL ℝ (intervalTraceData 0 n (fun _ => 1))

theorem cellPrefixL_apply (n : ℕ) (w : TraceData) :
    cellPrefixL n w = ∑ j ∈ Finset.range n, w j := by
  simp [cellPrefixL, innerSL_apply_apply, intervalTraceData_inner]

theorem cellPrefixL_zero (w : TraceData) : cellPrefixL 0 w = 0 := by
  simp [cellPrefixL_apply]

theorem cellPrefixL_succ (n : ℕ) (w : TraceData) :
    cellPrefixL (n+1) w = cellPrefixL n w + w n := by
  simp only [cellPrefixL_apply, Finset.sum_range_succ]

theorem cellPrefixL_interval (a b : ℕ) (hab : a ≤ b) (w : TraceData) :
    ∑ j ∈ Finset.Ico a b, w j = cellPrefixL b w - cellPrefixL a w := by
  simpa only [cellPrefixL_apply] using Finset.sum_Ico_eq_sub (fun j => w j) hab

def traceGradient : TraceData →L[ℝ] TraceData :=
  ContinuousLinearMap.id ℝ TraceData - (sequenceRightShift ℝ).toContinuousLinearMap

theorem traceGradient_apply (w : TraceData) :
    traceGradient w = w - sequenceRightShift ℝ w := rfl

theorem traceGradient_zero (w : TraceData) : traceGradient w 0 = w 0 := by
  simp only [traceGradient_apply, lp.coeFn_sub, Pi.sub_apply, sequenceRightShift_zero, sub_zero]

theorem traceGradient_succ (w : TraceData) (k : ℕ) :
    traceGradient w (k+1) = w (k+1) - w k := by
  simp only [traceGradient_apply, lp.coeFn_sub, Pi.sub_apply, sequenceRightShift_succ]

theorem traceGradient_single (k : ℕ) (a : ℝ) :
    traceGradient (lp.single 2 k a) = lp.single 2 k a - lp.single 2 (k+1) a := by
  rw [traceGradient_apply, sequenceRightShift_single]

theorem cellPrefixL_gradient (k : ℕ) (v : TraceData) :
    cellPrefixL (k+1) (traceGradient v) = v k := by
  induction k with
  | zero => rw [cellPrefixL_succ, cellPrefixL_zero, traceGradient_zero, zero_add]
  | succ k ih => rw [cellPrefixL_succ, ih, traceGradient_succ]; ring

theorem traceGradient_of_prefix (w v : TraceData)
    (h : ∀ k, v k = cellPrefixL (k+1) w) : traceGradient v = w := by
  apply lp.ext
  funext k
  cases k with
  | zero => rw [traceGradient_zero, h, cellPrefixL_succ, cellPrefixL_zero, zero_add]
  | succ k => rw [traceGradient_succ, h, h, cellPrefixL_succ]; ring

theorem hasSum_unitCellSynthesis (w : TraceData) :
    HasSum (fun k => w k • unitCell k) (unitCellSynthesis w) :=
  orthonormal_unitCell.orthogonalFamily.hasSum_linearIsometry w

theorem primitive_unitCellSynthesis (n : ℕ) (w : TraceData) :
    primitive (unitCellSynthesis w) n = cellPrefixL n w := by
  classical
  have hs := (innerSL ℝ (prefixCell n)).hasSum (hasSum_unitCellSynthesis w)
  have h : HasSum (fun k => if k < n then w k else 0)
      (primitive (unitCellSynthesis w) n) := by
    simp only [innerSL_apply_apply, real_inner_smul_right] at hs
    simp only [inner_prefixCell_unitCell, mul_ite, mul_one, mul_zero] at hs
    simpa only [inner_prefixCell] using hs
  rw [← h.tsum_eq, cellPrefixL_apply]
  calc
    _ = ∑ k ∈ Finset.range n, (if k < n then w k else 0) := by
      apply tsum_eq_sum
      intro k hk
      simp only [Finset.mem_range] at hk
      exact if_neg hk
    _ = _ := Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))

theorem log_unitCellSynthesis (k : ℕ) (w : TraceData) :
    logPrimitive (unitCellSynthesis w) (Real.log ((k : ℝ)+1)) = cellPrefixL (k+1) w := by
  rw [logPrimitive, Real.exp_log (by positivity)]
  simpa only [Nat.cast_add, Nat.cast_one] using primitive_unitCellSynthesis (k+1) w

theorem unitCellSynthesis_gradient (v : TraceData) :
    unitCellSynthesis (traceGradient v) = integerExtension v := rfl

theorem traceData_tail_constant_zero (w : TraceData) (a : ℕ) (c : ℝ)
    (h : ∀ n, w (a+n) = c) : c = 0 := by
  have hs : Summable (fun n => (w n)^2) := by
    simpa only [Real.inner_apply, pow_two] using (lp.summable_inner (𝕜 := ℝ) w w)
  have ht := (tendsto_add_atTop_iff_nat a).2 hs.tendsto_atTop_zero
  have ht' : Tendsto (fun _ : ℕ => c^2) atTop (𝓝 0) := by
    simpa only [Nat.add_comm _ a, h] using ht
  have he : (0 : ℝ) = c^2 := tendsto_nhds_unique ht' tendsto_const_nhds
  exact sq_eq_zero_iff.mp he.symm

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
