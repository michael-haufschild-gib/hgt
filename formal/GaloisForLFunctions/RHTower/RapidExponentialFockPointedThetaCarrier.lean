import GaloisForLFunctions.RHTower.RapidExponentialMomentFockThetaTrace
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCompactOpen
import GaloisForLFunctions.HTGeometry.ContinuousMapLocallyConvex

/-!
# Pointed rapid exponential-Fock theta carrier

For `0 < a < 1/2`, vertical-strip estimates bundle the rapid theta trace as a continuous linear
map from the exact moment-Fock Hilbert carrier to the compact-open space of entire functions.  The
distinguished constant vector retains the completed critical-line zeta trace.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Rapid theta trace as a compact-open continuous function. -/
def rapidExponentialMomentFockThetaTraceContinuousMap
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) : C(ℂ, ℂ) :=
  ⟨rapidExponentialMomentFockThetaTrace a ha f,
    (differentiable_rapidExponentialMomentFockThetaTrace a ha haHalf f).continuous⟩

@[simp] theorem rapidExponentialMomentFockThetaTraceContinuousMap_apply
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) (z : ℂ) :
    rapidExponentialMomentFockThetaTraceContinuousMap a ha haHalf f z =
      rapidExponentialMomentFockThetaTrace a ha f z := rfl

/-- Algebraic rapid theta trace into the compact-open ambient continuous-map space. -/
def rapidExponentialMomentFockThetaTraceCompactOpenLinearMap
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) : MomentFock →ₗ[ℂ] C(ℂ, ℂ) where
  toFun := rapidExponentialMomentFockThetaTraceContinuousMap a ha haHalf
  map_add' f g := by
    ext z
    exact rapidExponentialMomentFockThetaTrace_add a ha haHalf f g z
  map_smul' c f := by
    ext z
    exact rapidExponentialMomentFockThetaTrace_smul a ha c f z

/-- Vertical-strip bounds give compact-open continuity. -/
theorem continuous_rapidExponentialMomentFockThetaTraceCompactOpenLinearMap
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) :
    Continuous (rapidExponentialMomentFockThetaTraceCompactOpenLinearMap a ha haHalf) := by
  apply continuous_of_continuousAt_zero
    (rapidExponentialMomentFockThetaTraceCompactOpenLinearMap a ha haHalf)
  rw [ContinuousAt, map_zero]
  change Tendsto
    (rapidExponentialMomentFockThetaTraceCompactOpenLinearMap a ha haHalf)
    (nhds 0) (nhds 0)
  rw [HTGeometry.hasBasis_nhds_zero_continuousMap.tendsto_right_iff]
  rintro ⟨K, ε⟩ ⟨hK, hε⟩
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (f := fun z : ℂ => z.im) Complex.continuous_im.continuousOn
  let A : ℝ := max 0 R
  let C : ℝ := rapidExponentialMomentFockThetaTraceWeightBound a (2 * Real.pi * A)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact rapidExponentialMomentFockThetaTraceWeightBound_nonneg _ _
  have hden : 0 < C + 1 := by linarith
  filter_upwards [Metric.ball_mem_nhds (0 : MomentFock) (div_pos hε hden)] with f hf
  intro z hzK
  have hfNorm : ‖f‖ < ε / (C + 1) := by
    simpa [Metric.mem_ball, dist_zero_right] using hf
  have hz : |z.im| ≤ A := by
    have hzR := hR z hzK
    rw [Real.norm_eq_abs] at hzR
    exact hzR.trans (le_max_right 0 R)
  have htrace := norm_rapidExponentialMomentFockThetaTrace_le_verticalStrip
    a ha haHalf f hz
  change ‖rapidExponentialMomentFockThetaTrace a ha f z‖ < ε
  calc
    ‖rapidExponentialMomentFockThetaTrace a ha f z‖ ≤ C * ‖f‖ := by
      simpa [C] using htrace
    _ ≤ (C + 1) * ‖f‖ := by
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f)
    _ < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left hfNorm hden
    _ = ε := by field_simp

/-- Entire rapid theta trace as a continuous linear compact-open map. -/
def rapidExponentialMomentFockThetaTraceCompactOpen
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) :
    MomentFock →L[ℂ] DeningerCompactOpenEntire where
  toFun f :=
    ⟨rapidExponentialMomentFockThetaTraceContinuousMap a ha haHalf f,
      differentiable_rapidExponentialMomentFockThetaTrace a ha haHalf f⟩
  map_add' f g := by
    ext z
    exact rapidExponentialMomentFockThetaTrace_add a ha haHalf f g z
  map_smul' c f := by
    ext z
    exact rapidExponentialMomentFockThetaTrace_smul a ha c f z
  cont := by
    exact Continuous.subtype_mk
      (continuous_rapidExponentialMomentFockThetaTraceCompactOpenLinearMap a ha haHalf)
      (fun f => differentiable_rapidExponentialMomentFockThetaTrace a ha haHalf f)

@[simp] theorem rapidExponentialMomentFockThetaTraceCompactOpen_apply
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) (z : ℂ) :
    rapidExponentialMomentFockThetaTraceCompactOpen a ha haHalf f z =
      rapidExponentialMomentFockThetaTrace a ha f z := rfl

/-- Exact completed critical trace of the distinguished constant vector. -/
theorem completedRiemannZeta₀_critical_eq_rapidExponentialMomentFockThetaCarrier_one
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * Complex.I) =
      rapidExponentialMomentFockThetaTraceCompactOpen a ha haHalf
        (rapidExponentialMomentFockOne a ha)
          ((t / (4 * Real.pi) : ℝ) : ℂ) / 2 := by
  simpa using completedRiemannZeta₀_critical_eq_rapidExponentialMomentFockThetaTrace_one
    a ha t

end

end RHTower
