import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHeightLaplacian
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCutoffCommutator

/-! The full differential cutoff source as its actual smooth height field. -/
open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMCuspProjection
noncomputable section

def powerCutoffHeight (k : ℂ) (y : ℝ) : ℂ := cutoffPower k ![0,y]

theorem cutoffPower_low (k : ℂ) (z : Fin 2 → ℝ) (hz : z 1 ≤ 2) :
    cutoffPower k z = 0 := by
  unfold cutoffPower cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

theorem powerCutoffHeight_smooth (k : ℂ) : ContDiff ℝ ∞ (powerCutoffHeight k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 1 < y
  · have hz : ![0,y] ∈ domain := by change 0 < y; linarith
    have hp : ContDiffOn ℝ ∞ (cutoffPower k) domain :=
      sourceCutoff_smooth.contDiffOn.mul (height_cpow_contDiffOn k ∞)
    have hf := hp.contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
    have hc : ContDiff ℝ ∞ (fun t : ℝ => (![0,t] : Fin 2 → ℝ)) := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact contDiff_const
      · exact contDiff_id
    exact hf.comp y hc.contDiffAt
  · have he : powerCutoffHeight k =ᶠ[𝓝 y] (fun _ => 0) := by
      have h2 : y < 2 := by linarith
      filter_upwards [isOpen_Iio.mem_nhds h2] with t ht
      exact cutoffPower_low k ![0,t] ht.le
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem cutoffCommutator_height (k : ℂ) (z : Fin 2 → ℝ) :
    cutoffCommutator k z = (z 1:ℂ)^(2 : ℕ)*deriv (deriv (powerCutoffHeight k)) (z 1)-
      k*(k-1)*powerCutoffHeight k (z 1) := by
  have he : cutoffPower k = fun w => powerCutoffHeight k (w 1) := rfl
  rw [cutoffCommutator,he,height_laplacian _ (powerCutoffHeight_smooth k)]
  dsimp [powerCutoffHeight,cutoffPower,cutoff]
  ring

theorem cutoffCommutator_low (k : ℂ) (z : Fin 2 → ℝ) (hz : z 1 < 2) :
    cutoffCommutator k z = 0 := by
  have he : cutoffPower k =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hz] with y hy
    exact cutoffPower_low k y hy.le
  rw [cutoffCommutator,hyperbolicLaplacian_congr he]
  rw [height_laplacian (fun _ : ℝ => (0:ℂ)) contDiff_const z]
  unfold cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

theorem cutoffCommutator_height_continuous (k : ℂ) :
    Continuous (fun y : ℝ => cutoffCommutator k ![0,y]) := by
  have hdd := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp (powerCutoffHeight_smooth k)).2).2.continuous
  have he : (fun y : ℝ => cutoffCommutator k ![0,y]) = fun y : ℝ =>
      (y:ℂ)^(2 : ℕ)*deriv (deriv (powerCutoffHeight k)) y-k*(k-1)*powerCutoffHeight k y := by
    funext y
    exact cutoffCommutator_height k ![0,y]
  rw [he]
  exact ((Complex.continuous_ofReal.pow 2).mul hdd).sub
    (continuous_const.mul (powerCutoffHeight_smooth k).continuous)

theorem powerCutoffHeight_low_germ (k : ℂ) :
    powerCutoffHeight k =ᶠ[𝓝 (1:ℝ)] (fun _ => 0) := by
  filter_upwards [isOpen_Iio.mem_nhds (show (1:ℝ)<2 by norm_num)] with y hy
  exact cutoffPower_low k ![0,y] hy.le

theorem powerCutoffHeight_high_germ (k : ℂ) :
    powerCutoffHeight k =ᶠ[𝓝 (4:ℝ)] (fun y => (y:ℂ)^k) := by
  filter_upwards [isOpen_Ioi.mem_nhds (show (3:ℝ)<4 by norm_num)] with y hy
  change 3 < y at hy
  dsimp [powerCutoffHeight,cutoffPower,cutoff]
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  simp

end
end RHTower.D4BMJointSource
