import GaloisForLFunctions.HTGeometry.PaperFourierLiteralConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # A two-chamber profile with arbitrary wall value

The profile is minus one to the left of the midpoint and plus one to its right.
Changing its wall value changes neither its measure class nor any Fourier coefficient.
Every such profile has a genuine jump, so continuous Fourier cutoffs cannot converge uniformly.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal

/-- The two chamber signs, retaining an arbitrary value at the separating wall. -/
def paperIntervalWallStep (w : ℂ) (x : ℝ) : ℂ :=
  if x < 1 / 2 then -1 else if 1 / 2 < x then 1 else w

theorem paperIntervalWallStep_wall (w : ℂ) : paperIntervalWallStep w (1 / 2) = w := by
  simp [paperIntervalWallStep]

theorem paperIntervalWallStep_measurable (w : ℂ) : Measurable (paperIntervalWallStep w) := by
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

theorem paperIntervalWallStep_norm_le (w : ℂ) (x : ℝ) :
    ‖paperIntervalWallStep w x‖ ≤ max 1 ‖w‖ := by
  unfold paperIntervalWallStep
  split_ifs
  · simpa only [norm_neg, norm_one] using le_max_left (1 : ℝ) ‖w‖
  · simpa only [norm_one] using le_max_left (1 : ℝ) ‖w‖
  · exact le_max_right _ _

theorem paperIntervalWallStep_memLp (w : ℂ) :
    MemLp (paperIntervalWallStep w) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound (paperIntervalWallStep_measurable w).aestronglyMeasurable _
    (Eventually.of_forall (paperIntervalWallStep_norm_le w))

theorem paperIntervalWallStep_ae (w v : ℂ) :
    paperIntervalWallStep w =ᵐ[volume] paperIntervalWallStep v := by
  filter_upwards [volume.ae_ne (1 / 2 : ℝ)] with x hx
  rcases lt_or_gt_of_ne hx with h | h
  · simp only [paperIntervalWallStep, if_pos h]
  · simp only [paperIntervalWallStep, if_neg (not_lt.mpr h.le), if_pos h]

theorem paperIntervalWallStep_coefficient (w v : ℂ) (k : ℤ) :
    l2Pair (fourierChar k) (paperIntervalWallStep w) =
      l2Pair (fourierChar k) (paperIntervalWallStep v) := by
  unfold l2Pair
  apply intervalIntegral.integral_congr_ae
  filter_upwards [paperIntervalWallStep_ae w v] with x hx
  exact fun _ => congrArg ((starRingEnd ℂ) (fourierChar k x) * ·) hx

/-- Every finite Fourier observation is blind to the point value at the wall. -/
theorem paperIntervalWallStep_partialSum (w v : ℂ) (N : ℕ) (x : ℝ) :
    fourierPartialSum (paperIntervalWallStep w) N x =
      fourierPartialSum (paperIntervalWallStep v) N x := by
  simp only [fourierPartialSum, paperIntervalWallStep_coefficient w v]

theorem paperIntervalWallStep_reflect (x : ℝ) :
    paperIntervalWallStep 0 (1 - x) = -paperIntervalWallStep 0 x := by
  rcases lt_trichotomy x (1 / 2) with h | rfl | h
  · have h' : 1 / 2 < 1 - x := by linarith
    simp only [paperIntervalWallStep, if_pos h, if_neg (not_lt.mpr h'.le), if_pos h', neg_neg]
  · norm_num [paperIntervalWallStep]
  · have h' : 1 - x < 1 / 2 := by linarith
    simp only [paperIntervalWallStep, if_pos h', if_neg (not_lt.mpr h.le), if_pos h]

theorem paperIntervalWallStep_not_continuousAt (w : ℂ) :
    ¬ ContinuousAt (paperIntervalWallStep w) (1 / 2) := by
  intro hc
  have hl : Tendsto (paperIntervalWallStep w) (𝓝[<] (1 / 2 : ℝ)) (𝓝 (-1)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_Iio] at hx
    simp only [paperIntervalWallStep, if_pos hx]
  have hr : Tendsto (paperIntervalWallStep w) (𝓝[>] (1 / 2 : ℝ)) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_Ioi] at hx
    simp only [paperIntervalWallStep, if_neg (not_lt.mpr hx.le), if_pos hx]
  have hleft := tendsto_nhds_unique hl (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hright := tendsto_nhds_unique hr (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hbad := hleft.trans hright.symm
  norm_num at hbad

/-- The continuous symmetric cutoffs never converge uniformly across the jump. -/
theorem paperIntervalWallStep_not_uniform (w : ℂ) :
    ¬ TendstoUniformlyOn (fun N => fourierPartialSum (paperIntervalWallStep w) N)
      (paperIntervalWallStep w) atTop (Icc (0 : ℝ) 1) := by
  intro h
  have hc := h.continuousOn (Eventually.of_forall (fun N =>
    (continuous_fourierPartialSum (paperIntervalWallStep w) N).continuousOn)).frequently
  exact paperIntervalWallStep_not_continuousAt w
    ((hc (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)).continuousAt
      (Icc_mem_nhds (by norm_num) (by norm_num)))

end
end GaloisForLFunctions.HTGeometry
